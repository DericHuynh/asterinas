// SPDX-License-Identifier: MPL-2.0

//! Owned, all-or-nothing UID/GID/project quota planning.
//! A reservation owns its complete ledger, so another ledger cannot accept its
//! completion and cancellation cannot race a second reservation. Runtime worker
//! locking and atomic journal publication of inode and quota images remain
//! separate. Logical commit here is not a device durability acknowledgement.

use vstd::prelude::*;
use crate::quota_v2::{self, QuotaType, Record};

verus! {

pub const MAX_ACCOUNTS: usize = 4096;
pub const MAX_ACCOUNT: u64 = 9223372036854775807;

#[derive(Clone, Copy)]
pub struct Key { pub kind: QuotaType, pub id: u32 }

#[derive(Clone, Copy)]
pub struct Seed { pub kind: QuotaType, pub record: Record, pub block_grace: u32, pub inode_grace: u32 }

#[derive(Clone, Copy)]
pub struct Snapshot {
    pub seed: Seed, pub reserved_space: u64, pub reserved_inodes: u64,
}

#[derive(Clone, Copy)]
pub enum Error {
    InvalidAccount, MissingAccount, DuplicateSubject, TooManySubjects,
    InvalidClock, Arithmetic, BlockHardLimit, InodeHardLimit,
    BlockGraceExpired, InodeGraceExpired, PreallocationSoftLimit,
    Underflow, ExceedsReservation, EpochExhausted,
}

#[derive(Clone, Copy)]
struct Account { seed: Seed, reserved_space: u64, reserved_inodes: u64 }

pub struct Book { accounts: Vec<Account>, epoch: u64 }

pub struct Reservation {
    book: Book, indices: Vec<usize>, staged: Vec<Account>,
    space: u64, inodes: u64, epoch: u64,
}

/// Immutable record images are available before publication, permitting the
/// caller to include exactly these images in its filesystem journal closure.
pub struct Prepared {
    book: Book, indices: Vec<usize>, after: Vec<Account>, epoch: u64,
}


/// Mathematical counters use unbounded naturals. Executable counters are
/// admitted only below MAX_ACCOUNT, including committed plus reserved usage.
pub open spec fn rank(key: Key) -> nat {
    (match key.kind { QuotaType::User => 0nat, QuotaType::Group => 1nat, QuotaType::Project => 2nat })
        * 4294967296 + key.id as nat
}
pub open spec fn row_key(row: Snapshot) -> Key { Key { kind: row.seed.kind, id: row.seed.record.id } }
pub open spec fn seed_valid(seed: Seed) -> bool {
    let r = seed.record;
    r.inode_hard <= MAX_ACCOUNT && r.inode_soft <= MAX_ACCOUNT && r.current_inodes <= MAX_ACCOUNT
        && r.block_hard <= MAX_ACCOUNT / 1024 && r.block_soft <= MAX_ACCOUNT / 1024
        && r.current_space <= MAX_ACCOUNT && r.block_time <= MAX_ACCOUNT && r.inode_time <= MAX_ACCOUNT
}
pub open spec fn row_valid(row: Snapshot) -> bool {
    seed_valid(row.seed)
        && row.seed.record.current_space as nat + row.reserved_space <= MAX_ACCOUNT
        && row.seed.record.current_inodes as nat + row.reserved_inodes <= MAX_ACCOUNT
}
pub open spec fn sorted(rows: Seq<Snapshot>) -> bool {
    forall|i: int, j: int| 0 <= i < j < rows.len()
        ==> rank(row_key(rows[i])) < rank(row_key(rows[j]))
}
pub open spec fn ledger_valid(rows: Seq<Snapshot>) -> bool {
    rows.len() <= MAX_ACCOUNTS && sorted(rows)
        && forall|i: int| 0 <= i < rows.len() ==> row_valid(rows[i])
            && rows[i].reserved_space == 0 && rows[i].reserved_inodes == 0
}
pub open spec fn rows_contain_seed(rows: Seq<Snapshot>, seed: Seed) -> bool {
    exists|j: int| 0 <= j < rows.len() && #[trigger] rows[j].seed == seed
}
pub open spec fn input_contains_seed(seeds: Seq<Seed>, seed: Seed) -> bool {
    exists|j: int| 0 <= j < seeds.len() && #[trigger] seeds[j] == seed
}
pub open spec fn keys_contain(keys: Seq<Key>, key: Key) -> bool {
    exists|i: int| 0 <= i < keys.len() && rank(keys[i]) == rank(key)
}
pub open spec fn subjects_model(keys: Seq<Key>) -> bool {
    keys.len() <= 3 && forall|i: int, j: int| 0 <= i < j < keys.len() ==> keys[i].kind != keys[j].kind
}
pub open spec fn untimed(record: Record) -> Record { Record { block_time: 0, inode_time: 0, ..record } }
pub open spec fn same_static(a: Snapshot, b: Snapshot) -> bool {
    a.seed.kind == b.seed.kind && a.seed.block_grace == b.seed.block_grace
        && a.seed.inode_grace == b.seed.inode_grace && untimed(a.seed.record) == untimed(b.seed.record)
}
pub open spec fn cleared(a: Snapshot) -> Snapshot {
    let r = a.seed.record;
    let space = r.current_space as nat + a.reserved_space;
    let inodes = r.current_inodes as nat + a.reserved_inodes;
    Snapshot { seed: Seed { record: Record {
        block_time: if r.block_soft == 0 || space <= r.block_soft as nat * 1024 { 0 } else { r.block_time },
        inode_time: if r.inode_soft == 0 || inodes <= r.inode_soft { 0 } else { r.inode_time },
        ..r }, ..a.seed }, ..a }
}
pub open spec fn charged(a: Snapshot, space: u64, inodes: u64, now: u64, preallocation: bool)
    -> Option<Snapshot>
{
    let r = a.seed.record;
    let total_space = r.current_space as nat + a.reserved_space + space;
    let total_inodes = r.current_inodes as nat + a.reserved_inodes + inodes;
    let block_cross = space > 0 && r.block_soft != 0 && total_space > r.block_soft as nat * 1024;
    let inode_cross = inodes > 0 && r.inode_soft != 0 && total_inodes > r.inode_soft;
    let block_start = block_cross && r.block_time == 0;
    let inode_start = inode_cross && r.inode_time == 0;
    if !seed_valid(a.seed) || total_space > MAX_ACCOUNT || total_inodes > MAX_ACCOUNT
        || (space > 0 && r.block_hard != 0 && total_space > r.block_hard as nat * 1024)
        || (inodes > 0 && r.inode_hard != 0 && total_inodes > r.inode_hard)
        || (block_cross && r.block_time != 0 && now >= r.block_time)
        || (inode_cross && r.inode_time != 0 && now >= r.inode_time)
        || (block_start && preallocation)
        || (block_start && now as nat + a.seed.block_grace > MAX_ACCOUNT)
        || (inode_start && now as nat + a.seed.inode_grace > MAX_ACCOUNT) { None }
    else { Some(Snapshot {
        seed: Seed { record: Record {
            block_time: if block_start { (now as nat + a.seed.block_grace) as u64 } else { r.block_time },
            inode_time: if inode_start { (now as nat + a.seed.inode_grace) as u64 } else { r.inode_time },
            ..r }, ..a.seed },
        reserved_space: (a.reserved_space as nat + space) as u64,
        reserved_inodes: (a.reserved_inodes as nat + inodes) as u64,
    }) }
}
pub open spec fn finished(a: Snapshot, reserved_space: u64, reserved_inodes: u64,
    actual_space: u64, actual_inodes: u64) -> Option<Snapshot>
{
    if actual_space > reserved_space || actual_inodes > reserved_inodes
        || a.reserved_space < reserved_space || a.reserved_inodes < reserved_inodes
        || a.seed.record.current_space as nat + actual_space > MAX_ACCOUNT
        || a.seed.record.current_inodes as nat + actual_inodes > MAX_ACCOUNT { None }
    else { Some(cleared(Snapshot {
        seed: Seed { record: Record {
            current_space: (a.seed.record.current_space as nat + actual_space) as u64,
            current_inodes: (a.seed.record.current_inodes as nat + actual_inodes) as u64,
            ..a.seed.record }, ..a.seed },
        reserved_space: (a.reserved_space as nat - reserved_space) as u64,
        reserved_inodes: (a.reserved_inodes as nat - reserved_inodes) as u64,
    })) }
}
pub open spec fn freed(a: Snapshot, space: u64, inodes: u64) -> Option<Snapshot> {
    if a.seed.record.current_space < space || a.seed.record.current_inodes < inodes { None }
    else { Some(cleared(Snapshot {
        seed: Seed { record: Record {
            current_space: (a.seed.record.current_space as nat - space) as u64,
            current_inodes: (a.seed.record.current_inodes as nat - inodes) as u64, ..a.seed.record }, ..a.seed }, ..a
    })) }
}
pub open spec fn transferred_row(row: Snapshot, from: Seq<Key>, to: Seq<Key>,
    space: u64, inodes: u64, now: u64) -> Option<Snapshot>
{
    if keys_contain(from, row_key(row)) && !keys_contain(to, row_key(row)) { freed(row, space, inodes) }
    else if !keys_contain(from, row_key(row)) && keys_contain(to, row_key(row)) {
        match charged(row, space, inodes, now, false) {
            Some(a) => finished(a, space, inodes, space, inodes), None => None,
        }
    } else { Some(row) }
}
pub open spec fn transferred_rows(rows: Seq<Snapshot>, from: Seq<Key>, to: Seq<Key>,
    space: u64, inodes: u64, now: u64) -> Seq<Snapshot>
{
    Seq::new(rows.len(), |i: int| transferred_row(rows[i], from, to, space, inodes, now).unwrap())
}
pub open spec fn distinct_indices(indices: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j]
}
pub open spec fn apply_updates(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>) -> Seq<Snapshot>
    decreases indices.len(),
{
    if indices.len() == 0 || indices.len() != after.len() { rows }
    else { apply_updates(rows, indices.drop_last(), after.drop_last()).update(indices.last() as int, after.last()) }
}
pub open spec fn publication_valid(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>) -> bool {
    indices.len() == after.len() && indices.len() <= 6 && distinct_indices(indices)
        && forall|i: int| 0 <= i < indices.len() ==> indices[i] < rows.len()
            && row_valid(after[i]) && after[i].reserved_space == 0 && after[i].reserved_inodes == 0
            && rank(row_key(after[i])) == rank(row_key(rows[indices[i] as int]))
}
spec fn account_view(a: Account) -> Snapshot {
    Snapshot { seed: a.seed, reserved_space: a.reserved_space, reserved_inodes: a.reserved_inodes }
}
spec fn account_views(accounts: Seq<Account>) -> Seq<Snapshot> {
    accounts.map(|i: int, a: Account| account_view(a))
}
spec fn insertion_sorted(rows: Seq<Snapshot>, hole: int) -> bool {
    0 <= hole < rows.len()
        && (forall|i: int, j: int| 0 <= i < j < rows.len() && i != hole && j != hole
            ==> rank(row_key(rows[i])) < rank(row_key(rows[j])))
        && (forall|j: int| hole < j < rows.len() ==> rank(row_key(rows[hole])) < rank(row_key(rows[j])))
        && (forall|i: int, j: int| 0 <= i < j < rows.len() ==> rank(row_key(rows[i])) != rank(row_key(rows[j])))
}
proof fn insertion_done(rows: Seq<Snapshot>, hole: int)
    requires insertion_sorted(rows, hole),
        hole == 0 || rank(row_key(rows[hole - 1])) < rank(row_key(rows[hole])),
    ensures sorted(rows),
{
    assert forall|i: int, j: int| 0 <= i < j < rows.len()
        implies rank(row_key(rows[i])) < rank(row_key(rows[j])) by {
        if j == hole && i < hole - 1 {
            assert(rank(row_key(rows[i])) < rank(row_key(rows[hole - 1])));
        }
    }
}
proof fn insertion_step(rows: Seq<Snapshot>, hole: int)
    requires insertion_sorted(rows, hole), 0 < hole,
        !(rank(row_key(rows[hole - 1])) < rank(row_key(rows[hole]))),
    ensures insertion_sorted(rows.update(hole - 1, rows[hole]).update(hole, rows[hole - 1]), hole - 1),
{
    let next = rows.update(hole - 1, rows[hole]).update(hole, rows[hole - 1]);
    assert forall|i: int, j: int| 0 <= i < j < next.len() && i != hole - 1 && j != hole - 1
        implies rank(row_key(next[i])) < rank(row_key(next[j])) by {
        if i == hole && j > hole { assert(rank(row_key(rows[hole - 1])) < rank(row_key(rows[j]))); }
        if j == hole && i < hole - 1 { assert(rank(row_key(rows[i])) < rank(row_key(rows[hole - 1]))); }
    }
    assert forall|j: int| hole - 1 < j < next.len()
        implies #[trigger] rank(row_key(next[j])) > rank(row_key(next[hole - 1])) by {
        if j == hole { assert(rank(row_key(rows[hole])) < rank(row_key(rows[hole - 1]))); }
    }
    assert forall|i: int, j: int| 0 <= i < j < next.len()
        implies rank(row_key(next[i])) != rank(row_key(next[j])) by {
        let a = if i == hole - 1 { hole } else if i == hole { hole - 1 } else { i };
        let b = if j == hole - 1 { hole } else if j == hole { hole - 1 } else { j };
        assert(a != b);
        if a < b { assert(rank(row_key(rows[a])) != rank(row_key(rows[b]))); }
        else { assert(rank(row_key(rows[b])) != rank(row_key(rows[a]))); }
    }
}
proof fn publication_preserves_ledger(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>)
    requires ledger_valid(rows), publication_valid(rows, indices, after),
    ensures ledger_valid(apply_updates(rows, indices, after)),
    decreases indices.len(),
{
    if indices.len() > 0 {
        publication_preserves_ledger(rows, indices.drop_last(), after.drop_last());
        let prior = apply_updates(rows, indices.drop_last(), after.drop_last());
        let at = indices.last() as int;
        assert forall|i: int| 0 <= i < rows.len()
            implies rank(row_key(prior[i])) == rank(row_key(rows[i])) by {
            updates_preserve_rank(rows, indices.drop_last(), after.drop_last(), i);
        }
        assert forall|i: int, j: int| 0 <= i < j < rows.len()
            implies rank(row_key(prior.update(at, after.last())[i])) < rank(row_key(prior.update(at, after.last())[j])) by {
            assert(rank(row_key(prior[i])) == rank(row_key(rows[i])));
            assert(rank(row_key(prior[j])) == rank(row_key(rows[j])));
        }
    }
}
proof fn updates_preserve_rank(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>, i: int)
    requires publication_valid(rows, indices, after), 0 <= i < rows.len(),
    ensures apply_updates(rows, indices, after).len() == rows.len(),
        rank(row_key(apply_updates(rows, indices, after)[i])) == rank(row_key(rows[i])),
    decreases indices.len(),
{
    if indices.len() > 0 {
        updates_preserve_rank(rows, indices.drop_last(), after.drop_last(), i);
    }
}

impl Book {
    pub closed spec fn view(&self) -> Seq<Snapshot> { account_views(self.accounts@) }
    pub closed spec fn epoch_view(&self) -> u64 { self.epoch }
    pub open spec fn wf(&self) -> bool { ledger_valid(self.view()) }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}
impl Reservation {
    pub closed spec fn base_valid(&self) -> bool { self.book.wf() }
    pub closed spec fn base_epoch(&self) -> u64 { self.book.epoch_view() }
    pub closed spec fn before(&self) -> Seq<Snapshot> { self.book.view() }
    pub closed spec fn indices_view(&self) -> Seq<usize> { self.indices@ }
    pub closed spec fn staged_view(&self) -> Seq<Snapshot> { account_views(self.staged@) }
    pub closed spec fn space_view(&self) -> u64 { self.space }
    pub closed spec fn inodes_view(&self) -> u64 { self.inodes }
    pub closed spec fn epoch_view(&self) -> u64 { self.epoch }
    pub open spec fn wf(&self) -> bool {
        self.base_valid() && self.base_epoch() < 0xffff_ffff_ffff_ffff
            && self.epoch_view() as nat == self.base_epoch() as nat + 1
            && 0 < self.indices_view().len() <= 3
            && self.indices_view().len() == self.staged_view().len()
            && distinct_indices(self.indices_view())
            && forall|i: int| 0 <= i < self.indices_view().len()
                ==> self.indices_view()[i] < self.before().len()
                    && row_valid(self.staged_view()[i])
                    && same_static(self.before()[self.indices_view()[i] as int], self.staged_view()[i])
                    && self.staged_view()[i].reserved_space == self.space_view()
                    && self.staged_view()[i].reserved_inodes == self.inodes_view()
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}
impl Prepared {
    pub closed spec fn base_valid(&self) -> bool { self.book.wf() }
    pub closed spec fn base_epoch(&self) -> u64 { self.book.epoch_view() }
    pub closed spec fn before(&self) -> Seq<Snapshot> { self.book.view() }
    pub closed spec fn indices_view(&self) -> Seq<usize> { self.indices@ }
    pub closed spec fn after_view(&self) -> Seq<Snapshot> { account_views(self.after@) }
    pub closed spec fn epoch_view(&self) -> u64 { self.epoch }
    pub open spec fn publication(&self) -> Seq<Snapshot> {
        apply_updates(self.before(), self.indices_view(), self.after_view())
    }
    pub open spec fn wf(&self) -> bool {
        self.base_valid() && self.base_epoch() < 0xffff_ffff_ffff_ffff
            && self.epoch_view() as nat == self.base_epoch() as nat + 1
            && publication_valid(self.before(), self.indices_view(), self.after_view())
    }
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool { self.wf() }
}

pub fn key_rank(key: Key) -> (r: u64) ensures r as nat == rank(key), r < 12884901888 {
    let kind = match key.kind { QuotaType::User => 0u64, QuotaType::Group => 1u64, QuotaType::Project => 2u64 };
    kind * 4294967296 + key.id as u64
}

fn account_key(account: Account) -> (r: Key) ensures r == row_key(account_view(account)),
{ Key { kind: account.seed.kind, id: account.seed.record.id } }

fn add(a: u64, b: u64) -> (r: Option<u64>)
    ensures match r { Some(sum) => sum as nat == a as nat + b && sum <= MAX_ACCOUNT,
        None => a as nat + b > MAX_ACCOUNT },
{
    if a > MAX_ACCOUNT || b > MAX_ACCOUNT - a { None } else { Some(a + b) }
}

fn valid_seed(seed: Seed) -> (r: bool) ensures r == seed_valid(seed) {
    let r = seed.record;
    r.inode_hard <= MAX_ACCOUNT && r.inode_soft <= MAX_ACCOUNT && r.current_inodes <= MAX_ACCOUNT
        && r.block_hard <= MAX_ACCOUNT / 1024 && r.block_soft <= MAX_ACCOUNT / 1024
        && r.current_space <= MAX_ACCOUNT && r.block_time <= MAX_ACCOUNT && r.inode_time <= MAX_ACCOUNT
}

fn find(accounts: &[Account], key: Key) -> (r: Option<usize>)
    requires sorted(account_views(accounts@)),
    ensures match r {
        Some(i) => i < accounts.len() && rank(row_key(account_view(accounts@[i as int]))) == rank(key),
        None => forall|i: int| 0 <= i < accounts.len() ==> rank(row_key(account_view(accounts@[i]))) != rank(key),
    },
{
    let rank = key_rank(key);
    let mut low = 0usize; let mut high = accounts.len();
    while low < high
        invariant low <= high <= accounts.len(), sorted(account_views(accounts@)),
            rank as nat == crate::quota_reservation::rank(key),
            forall|i: int| 0 <= i < low ==> crate::quota_reservation::rank(row_key(account_view(accounts@[i]))) < rank,
            forall|i: int| high <= i < accounts.len() ==> crate::quota_reservation::rank(row_key(account_view(accounts@[i]))) >= rank,
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        let current = key_rank(account_key(accounts[mid]));
        if current < rank { low = mid + 1; } else { high = mid; }
    }
    if low < accounts.len() && key_rank(account_key(accounts[low])) == rank { Some(low) } else { None }
}

fn contains(keys: &[Key], key: Key) -> (r: bool) ensures r == keys_contain(keys@, key) {
    let mut i = 0usize;
    while i < keys.len()
        invariant i <= keys.len(),
            forall|j: int| 0 <= j < i ==> rank(keys@[j]) != rank(key),
        decreases keys.len() - i,
    { if key_rank(keys[i]) == key_rank(key) { return true; } i += 1; }
    false
}

fn subjects_valid(keys: &[Key]) -> (r: bool) ensures r == subjects_model(keys@) {
    if keys.len() > 3 { return false; }
    let mut i = 0usize;
    while i < keys.len()
        invariant i <= keys.len() <= 3,
            forall|a: int, b: int| 0 <= a < b < i ==> keys@[a].kind != keys@[b].kind,
        decreases keys.len() - i,
    {
        let mut j = 0usize;
        while j < i
            invariant j <= i < keys.len() <= 3,
                forall|a: int, b: int| 0 <= a < b < i ==> keys@[a].kind != keys@[b].kind,
                forall|a: int| 0 <= a < j ==> keys@[a].kind != keys@[i as int].kind,
            decreases i - j,
        {
            // There is at most one charge per quota type for one inode.
            if quota_v2::same_type(keys[j].kind, keys[i].kind) { return false; }
            j += 1;
        }
        i += 1;
    }
    true
}

fn clear_below_soft(mut account: Account) -> (r: Account)
    requires row_valid(account_view(account)),
    ensures account_view(r) == cleared(account_view(account)), row_valid(account_view(r)),
{
    if !valid_seed(account.seed) { return account; }
    let total_space = add(account.seed.record.current_space, account.reserved_space);
    let total_inodes = add(account.seed.record.current_inodes, account.reserved_inodes);
    let space_soft = account.seed.record.block_soft * 1024;
    if account.seed.record.block_soft == 0
        || match total_space { Some(total) => total <= space_soft, None => false } {
        account.seed.record.block_time = 0;
    }
    if account.seed.record.inode_soft == 0
        || match total_inodes { Some(total) => total <= account.seed.record.inode_soft, None => false } {
        account.seed.record.inode_time = 0;
    }
    account
}

fn charge(mut a: Account, space: u64, inodes: u64, now: u64, preallocation: bool) -> (r: Result<Account, Error>)
    ensures match r {
        Ok(after) => charged(account_view(a), space, inodes, now, preallocation) == Some(account_view(after))
            && row_valid(account_view(after)) && same_static(account_view(a), account_view(after)),
        Err(_) => charged(account_view(a), space, inodes, now, preallocation).is_none(),
    },
{
    if !valid_seed(a.seed) { return Err(Error::InvalidAccount); }
    let used_space = match add(a.seed.record.current_space, a.reserved_space) {
        Some(v) => v, None => { return Err(Error::Arithmetic); }
    };
    let used_inodes = match add(a.seed.record.current_inodes, a.reserved_inodes) {
        Some(v) => v, None => { return Err(Error::Arithmetic); }
    };
    let total_space = match add(used_space, space) { Some(v) => v, None => { return Err(Error::Arithmetic); } };
    let total_inodes = match add(used_inodes, inodes) { Some(v) => v, None => { return Err(Error::Arithmetic); } };
    if space > 0 {
        let hard = a.seed.record.block_hard * 1024;
        let soft = a.seed.record.block_soft * 1024;
        if hard != 0 && total_space > hard { return Err(Error::BlockHardLimit); }
        if soft != 0 && total_space > soft {
            if a.seed.record.block_time != 0 && now >= a.seed.record.block_time { return Err(Error::BlockGraceExpired); }
            if a.seed.record.block_time == 0 {
                if preallocation { return Err(Error::PreallocationSoftLimit); }
                a.seed.record.block_time = match add(now, a.seed.block_grace as u64) {
                    Some(v) => v, None => { return Err(Error::Arithmetic); }
                };
            }
        }
    }
    if inodes > 0 {
        if a.seed.record.inode_hard != 0 && total_inodes > a.seed.record.inode_hard { return Err(Error::InodeHardLimit); }
        if a.seed.record.inode_soft != 0 && total_inodes > a.seed.record.inode_soft {
            if a.seed.record.inode_time != 0 && now >= a.seed.record.inode_time { return Err(Error::InodeGraceExpired); }
            if a.seed.record.inode_time == 0 {
                a.seed.record.inode_time = match add(now, a.seed.inode_grace as u64) {
                    Some(v) => v, None => { return Err(Error::Arithmetic); }
                };
            }
        }
    }
    a.reserved_space = match add(a.reserved_space, space) { Some(v) => v, None => { return Err(Error::Arithmetic); } };
    a.reserved_inodes = match add(a.reserved_inodes, inodes) { Some(v) => v, None => { return Err(Error::Arithmetic); } };
    Ok(a)
}

fn finish(mut a: Account, reserved_space: u64, reserved_inodes: u64, actual_space: u64, actual_inodes: u64)
    -> (r: Option<Account>)
    requires row_valid(account_view(a)),
    ensures match r {
        Some(after) => finished(account_view(a), reserved_space, reserved_inodes, actual_space, actual_inodes)
                == Some(account_view(after)) && row_valid(account_view(after)),
        None => finished(account_view(a), reserved_space, reserved_inodes, actual_space, actual_inodes).is_none(),
    },
{
    if actual_space > reserved_space || actual_inodes > reserved_inodes
        || a.reserved_space < reserved_space || a.reserved_inodes < reserved_inodes { return None; }
    a.seed.record.current_space = match add(a.seed.record.current_space, actual_space) { Some(v) => v, None => { return None; } };
    a.seed.record.current_inodes = match add(a.seed.record.current_inodes, actual_inodes) { Some(v) => v, None => { return None; } };
    a.reserved_space -= reserved_space;
    a.reserved_inodes -= reserved_inodes;
    Some(clear_below_soft(a))
}

impl Book {
    pub fn new(seeds: &[Seed]) -> (r: Option<Self>)
        ensures match r {
            Some(book) => book.wf() && book.epoch_view() == 0 && book.view().len() == seeds.len()
                && (forall|i: int| 0 <= i < seeds.len() ==> #[trigger] rows_contain_seed(book.view(), seeds@[i]))
                && (forall|j: int| 0 <= j < book.view().len() ==> #[trigger] input_contains_seed(seeds@, book.view()[j].seed)),
            None => true,
        },
{
        if seeds.len() > MAX_ACCOUNTS { return None; }
        let mut accounts = Vec::<Account>::new(); let mut i = 0usize;
        while i < seeds.len()
            invariant i <= seeds.len() <= MAX_ACCOUNTS, accounts.len() == i,
                ledger_valid(account_views(accounts@)),
                (forall|k: int| 0 <= k < i ==> #[trigger] rows_contain_seed(account_views(accounts@), seeds@[k])),
                (forall|j: int| 0 <= j < accounts.len() ==> #[trigger] input_contains_seed(seeds@.subrange(0, i as int), accounts@[j].seed)),
            decreases seeds.len() - i,
        {
            let seed = seeds[i];
            if !valid_seed(seed) { return None; }
            let a = Account { seed, reserved_space: 0, reserved_inodes: 0 };
            if find(accounts.as_slice(), account_key(a)).is_some() { return None; }
            accounts.push(a); let mut j = accounts.len() - 1;
            while j > 0
                invariant j < accounts.len(), accounts.len() == i + 1 <= MAX_ACCOUNTS, i < seeds.len() <= MAX_ACCOUNTS,
                    insertion_sorted(account_views(accounts@), j as int),
                    forall|k: int| 0 <= k < accounts.len() ==> row_valid(account_view(accounts@[k]))
                        && accounts@[k].reserved_space == 0 && accounts@[k].reserved_inodes == 0,
                    (forall|k: int| 0 <= k <= i ==> #[trigger] rows_contain_seed(account_views(accounts@), seeds@[k])),
                    (forall|n: int| 0 <= n < accounts.len() ==> #[trigger] input_contains_seed(seeds@.subrange(0, i as int + 1), accounts@[n].seed)),
                decreases j,
            {
                if key_rank(account_key(accounts[j - 1])) < key_rank(account_key(accounts[j])) {
                    proof { insertion_done(account_views(accounts@), j as int); }
                    break;
                }
                let ghost before_swap = accounts@;
                proof { insertion_step(account_views(accounts@), j as int); }
                let old = accounts[j - 1]; accounts[j - 1] = accounts[j]; accounts[j] = old;
                proof {
                    assert(account_views(accounts@) =~= account_views(before_swap).update(j as int - 1,
                        account_view(before_swap[j as int])).update(j as int, account_view(before_swap[j as int - 1])));
                }
                j -= 1;
            }
            proof { if j == 0 { insertion_done(account_views(accounts@), 0); } }
            i += 1;
        }
        Some(Book { accounts, epoch: 0 })
    }

    pub fn epoch(&self) -> (r: u64) ensures self.wf(), r == self.epoch_view(),
    { proof { use_type_invariant(self); } self.epoch }

    pub fn len(&self) -> (r: usize) ensures self.wf(), r == self.view().len(), r <= MAX_ACCOUNTS,
    { proof { use_type_invariant(self); } self.accounts.len() }

    pub fn get(&self, key: Key) -> (r: Option<Snapshot>)
        ensures self.wf(), match r {
            Some(row) => row_valid(row) && row.reserved_space == 0 && row.reserved_inodes == 0
                && exists|i: int| 0 <= i < self.view().len() && self.view()[i] == row && rank(row_key(row)) == rank(key),
            None => forall|i: int| 0 <= i < self.view().len() ==> rank(row_key(self.view()[i])) != rank(key),
        },
    {
        proof { use_type_invariant(self); }
        match find(self.accounts.as_slice(), key) {
            Some(index) => {
                let a = self.accounts[index];
                Some(Snapshot { seed: a.seed, reserved_space: a.reserved_space, reserved_inodes: a.reserved_inodes })
            },
            None => None,
        }
    }

    /// A failed reservation returns the original ledger without any partial
    /// UID/GID/project charge. Grace is started only in the private candidate.
    pub fn reserve(self, keys: &[Key], space: u64, inodes: u64, now: u64, preallocation: bool)
        -> (r: Result<Reservation, (Book, Error)>)
        ensures match r {
            Ok(reservation) => reservation.wf() && reservation.before() == self.view()
                && reservation.epoch_view() as nat == self.epoch_view() as nat + 1
                && reservation.space_view() == space && reservation.inodes_view() == inodes
                && reservation.indices_view().len() == keys.len()
                && forall|i: int| 0 <= i < keys.len()
                    ==> rank(row_key(self.view()[reservation.indices_view()[i] as int])) == rank(keys@[i])
                        && charged(self.view()[reservation.indices_view()[i] as int], space, inodes, now, preallocation)
                            == Some(reservation.staged_view()[i]),
            Err((book, _)) => book.wf() && book.view() == self.view() && book.epoch_view() == self.epoch_view(),
        },
    {
        proof { use_type_invariant(&self); }
        if keys.len() == 0 || !subjects_valid(keys) { return Err((self, Error::DuplicateSubject)); }
        if now == 0 || now > MAX_ACCOUNT { return Err((self, Error::InvalidClock)); }
        if self.epoch == 0xffff_ffff_ffff_ffff { return Err((self, Error::EpochExhausted)); }
        let mut indices = Vec::<usize>::new(); let mut staged = Vec::<Account>::new(); let mut i = 0usize;
        while i < keys.len()
            invariant i <= keys.len() <= 3, indices.len() == i, staged.len() == i,
                self.wf(), 0 < keys.len(), subjects_model(keys@), self.epoch < 0xffff_ffff_ffff_ffff,
                distinct_indices(indices@),
                forall|j: int| 0 <= j < i ==> indices@[j] < self.view().len()
                    && rank(row_key(self.view()[indices@[j] as int])) == rank(keys@[j])
                    && charged(self.view()[indices@[j] as int], space, inodes, now, preallocation) == Some(account_view(staged@[j]))
                    && row_valid(account_view(staged@[j]))
                    && same_static(self.view()[indices@[j] as int], account_view(staged@[j]))
                    && staged@[j].reserved_space == space && staged@[j].reserved_inodes == inodes,
            decreases keys.len() - i,
        {
            let index = match find(self.accounts.as_slice(), keys[i]) {
                Some(v) => v, None => { return Err((self, Error::MissingAccount)); }
            };
            let after = match charge(self.accounts[index], space, inodes, now, preallocation) {
                Ok(v) => v, Err(error) => { return Err((self, error)); }
            };
            indices.push(index); staged.push(after); i += 1;
        }
        let epoch = self.epoch + 1;
        Ok(Reservation { book: self, indices, staged, space, inodes, epoch })
    }

    /// Stage ownership transfer without charging subjects common to both
    /// identities twice. Every decrement and limit check completes before the
    /// caller receives any candidate record image.
    pub fn transfer(self, from: &[Key], to: &[Key], space: u64, inodes: u64, now: u64)
        -> (r: Result<Prepared, (Book, Error)>)
        ensures match r {
            Ok(plan) => plan.wf() && plan.before() == self.view()
                && plan.epoch_view() as nat == self.epoch_view() as nat + 1
                && plan.publication() == transferred_rows(self.view(), from@, to@, space, inodes, now)
                && forall|i: int| 0 <= i < self.view().len()
                    ==> transferred_row(self.view()[i], from@, to@, space, inodes, now).is_some(),
            Err((book, _)) => book.wf() && book.view() == self.view() && book.epoch_view() == self.epoch_view(),
        },
    {
        proof { use_type_invariant(&self); }
        if !subjects_valid(from) || !subjects_valid(to) { return Err((self, Error::DuplicateSubject)); }
        if now == 0 || now > MAX_ACCOUNT { return Err((self, Error::InvalidClock)); }
        if self.epoch == 0xffff_ffff_ffff_ffff { return Err((self, Error::EpochExhausted)); }
        let mut indices = Vec::<usize>::new(); let mut after = Vec::<Account>::new(); let mut i = 0usize;
        while i < from.len()
            invariant i <= from.len() <= 3, indices.len() == after.len() <= 3, indices.len() <= i,
                self.wf(), self.epoch < 0xffff_ffff_ffff_ffff, subjects_model(from@), subjects_model(to@),
                publication_valid(self.view(), indices@, account_views(after@)),
                apply_updates(self.view(), indices@, account_views(after@))
                    == Seq::new(self.view().len(), |j: int|
                        if keys_contain(from@.subrange(0, i as int), row_key(self.view()[j]))
                            && !keys_contain(to@, row_key(self.view()[j])) {
                            freed(self.view()[j], space, inodes).unwrap()
                        } else { self.view()[j] }),
                forall|j: int| 0 <= j < self.view().len()
                    && keys_contain(from@.subrange(0, i as int), row_key(self.view()[j]))
                    && !keys_contain(to@, row_key(self.view()[j])) ==> freed(self.view()[j], space, inodes).is_some(),
            decreases from.len() - i,
        {
            let index = match find(self.accounts.as_slice(), from[i]) { Some(v) => v, None => { return Err((self, Error::MissingAccount)); } };
            if !contains(to, from[i]) {
                let mut a = self.accounts[index];
                if a.seed.record.current_space < space || a.seed.record.current_inodes < inodes { return Err((self, Error::Underflow)); }
                a.seed.record.current_space -= space; a.seed.record.current_inodes -= inodes;
                indices.push(index); after.push(clear_below_soft(a));
            }
            i += 1;
        }
        i = 0;
        while i < to.len()
            invariant i <= to.len() <= 3, indices.len() == after.len() <= 6, indices.len() <= from.len() + i,
                self.wf(), self.epoch < 0xffff_ffff_ffff_ffff, subjects_model(from@), subjects_model(to@),
                publication_valid(self.view(), indices@, account_views(after@)),
                (forall|j: int| #![trigger freed(self.view()[j], space, inodes)]
                    0 <= j < self.view().len() && keys_contain(from@, row_key(self.view()[j]))
                    && !keys_contain(to@, row_key(self.view()[j])) ==> freed(self.view()[j], space, inodes).is_some()),
                (forall|j: int| #![trigger transferred_row(self.view()[j], from@, to@, space, inodes, now)]
                    0 <= j < self.view().len() && !keys_contain(from@, row_key(self.view()[j]))
                    && keys_contain(to@.subrange(0, i as int), row_key(self.view()[j]))
                    ==> transferred_row(self.view()[j], from@, to@, space, inodes, now).is_some()),
                forall|j: int| 0 <= j < self.view().len()
                    ==> apply_updates(self.view(), indices@, account_views(after@))[j]
                        == if keys_contain(from@, row_key(self.view()[j])) && !keys_contain(to@, row_key(self.view()[j])) {
                            freed(self.view()[j], space, inodes).unwrap()
                        } else if !keys_contain(from@, row_key(self.view()[j]))
                            && keys_contain(to@.subrange(0, i as int), row_key(self.view()[j])) {
                            transferred_row(self.view()[j], from@, to@, space, inodes, now).unwrap()
                        } else { self.view()[j] },
            decreases to.len() - i,
        {
            let index = match find(self.accounts.as_slice(), to[i]) { Some(v) => v, None => { return Err((self, Error::MissingAccount)); } };
            if !contains(from, to[i]) {
                let a = match charge(self.accounts[index], space, inodes, now, false) { Ok(v) => v, Err(e) => { return Err((self, e)); } };
                let a = match finish(a, space, inodes, space, inodes) { Some(v) => v, None => { return Err((self, Error::Arithmetic)); } };
                indices.push(index); after.push(a);
            }
            i += 1;
        }
        let epoch = self.epoch + 1;
        Ok(Prepared { book: self, indices, after, epoch })
    }

    /// Free only committed usage. This is also an all-or-nothing journal plan;
    /// releasing an unowned byte/inode count cannot silently saturate to zero.
    pub fn release(self, keys: &[Key], space: u64, inodes: u64) -> (r: Result<Prepared, (Book, Error)>)
        ensures match r {
            Ok(plan) => plan.wf() && plan.before() == self.view()
                && plan.publication() == transferred_rows(self.view(), keys@, Seq::empty(), space, inodes, 1),
            Err((book, _)) => book.wf() && book.view() == self.view() && book.epoch_view() == self.epoch_view(),
        },
    {
        self.transfer(keys, &[], space, inodes, 1)
    }
}

impl Reservation {
    pub fn reservation_epoch(&self) -> (r: u64) ensures self.wf(), r == self.epoch_view(),
    { proof { use_type_invariant(self); } self.epoch }

    pub fn subjects(&self) -> (r: usize) ensures self.wf(), r == self.indices_view().len(), 0 < r <= 3,
    { proof { use_type_invariant(self); } self.indices.len() }

    pub fn preview(&self, index: usize) -> (r: Option<Snapshot>)
        ensures self.wf(), match r {
            Some(row) => index < self.staged_view().len() && row == self.staged_view()[index as int] && row_valid(row),
            None => index >= self.staged_view().len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.staged.len() { return None; }
        let a = self.staged[index];
        Some(Snapshot { seed: a.seed, reserved_space: a.reserved_space, reserved_inodes: a.reserved_inodes })
    }

    pub fn cancel_reservation(self) -> (r: Book)
        ensures r.wf(), r.view() == self.before(), r.epoch_view() == self.epoch_view(),
    {
        proof { use_type_invariant(&self); }
        let mut book = self.book; book.epoch = self.epoch; book
    }

    /// Actual use may be a prefix of a reservation. Surplus reservation is
    /// returned in every subject; it is never converted into a second charge.
    pub fn prepare(self, actual_space: u64, actual_inodes: u64) -> (r: Result<Prepared, (Book, Error)>)
        ensures match r {
            Ok(plan) => plan.wf() && plan.before() == self.before() && plan.epoch_view() == self.epoch_view()
                && plan.indices_view() == self.indices_view()
                && forall|i: int| 0 <= i < plan.after_view().len()
                    ==> finished(self.staged_view()[i], self.space_view(), self.inodes_view(), actual_space, actual_inodes)
                        == Some(plan.after_view()[i]),
            Err((book, _)) => book.wf() && book.view() == self.before() && book.epoch_view() == self.epoch_view(),
        },
    {
        proof { use_type_invariant(&self); }
        if actual_space > self.space || actual_inodes > self.inodes {
            return Err((self.cancel_reservation(), Error::ExceedsReservation));
        }
        let mut after = Vec::<Account>::new(); let mut i = 0usize;
        while i < self.staged.len()
            invariant i <= self.staged.len(), after.len() == i, self.wf(),
                actual_space <= self.space, actual_inodes <= self.inodes,
                publication_valid(self.before(), self.indices@.subrange(0, i as int), account_views(after@)),
                forall|j: int| 0 <= j < i
                    ==> finished(self.staged_view()[j], self.space, self.inodes, actual_space, actual_inodes)
                        == Some(account_view(after@[j])),
            decreases self.staged.len() - i,
        {
            let a = match finish(self.staged[i], self.space, self.inodes, actual_space, actual_inodes) {
                Some(v) => v, None => { return Err((self.cancel_reservation(), Error::Arithmetic)); }
            };
            after.push(a); i += 1;
        }
        Ok(Prepared { book: self.book, indices: self.indices, after, epoch: self.epoch })
    }
}

impl Prepared {
    pub fn prepared_epoch(&self) -> (r: u64) ensures self.wf(), r == self.epoch_view(),
    { proof { use_type_invariant(self); } self.epoch }

    pub fn updates_len(&self) -> (r: usize) ensures self.wf(), r == self.after_view().len(), r <= 6,
    { proof { use_type_invariant(self); } self.after.len() }

    pub fn update(&self, index: usize) -> (r: Option<Seed>)
        ensures self.wf(), match r {
            Some(seed) => index < self.after_view().len() && seed == self.after_view()[index as int].seed && seed_valid(seed),
            None => index >= self.after_view().len(),
        },
    {
        proof { use_type_invariant(self); }
        if index >= self.after.len() { None } else { Some(self.after[index].seed) }
    }

    pub fn cancel_prepared(self) -> (r: Book)
        ensures r.wf(), r.view() == self.before(), r.epoch_view() == self.epoch_view(),
    {
        proof { use_type_invariant(&self); }
        let mut book = self.book; book.epoch = self.epoch; book
    }

    /// Publish the logical ledger only. The filesystem adapter is responsible
    /// for first establishing the exact inode+quota journal commit boundary.
    pub fn commit(self) -> (r: Book)
        ensures r.wf(), r.view() == self.publication(), r.epoch_view() == self.epoch_view(),
    {
        proof {
            use_type_invariant(&self);
            publication_preserves_ledger(self.before(), self.indices_view(), self.after_view());
        }
        let ghost before = self.before();
        let ghost planned = self.publication();
        let mut book = self.book;
        if self.indices.len() != self.after.len() { return book; }
        let mut i = 0usize;
        // Validate the whole publication plan before touching a single row.
        while i < self.indices.len()
            invariant i <= self.indices.len(), self.indices.len() == self.after.len(),
                publication_valid(before, self.indices@, account_views(self.after@)),
                book.view() == before, ledger_valid(book.view()),
                planned == apply_updates(before, self.indices@, account_views(self.after@)), ledger_valid(planned),
            decreases self.indices.len() - i,
        {
            if self.indices[i] >= book.accounts.len() { return book; }
            let mut j = 0usize;
            while j < i
                invariant j <= i < self.indices.len(), distinct_indices(self.indices@),
                    publication_valid(before, self.indices@, account_views(self.after@)), book.view() == before, ledger_valid(planned),
                decreases i - j,
            { if self.indices[j] == self.indices[i] { return book; } j += 1; }
            i += 1;
        }
        i = 0;
        while i < self.indices.len()
            invariant i <= self.indices.len(), self.indices.len() == self.after.len(),
                publication_valid(before, self.indices@, account_views(self.after@)),
                account_views(book.accounts@) == apply_updates(before,
                    self.indices@.subrange(0, i as int), account_views(self.after@).subrange(0, i as int)),
                planned == apply_updates(before, self.indices@, account_views(self.after@)), ledger_valid(planned),
                book.accounts.len() == before.len(),
            decreases self.indices.len() - i,
        {
            book.accounts[self.indices[i]] = self.after[i]; i += 1;
        }
        book.epoch = self.epoch; book
    }
}

}
