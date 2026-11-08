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

proof fn rank_identifies_key(a: Key, b: Key)
    ensures rank(a) == rank(b) ==> a == b,
{
    if rank(a) == rank(b) {
        match (a.kind, b.kind) {
            (QuotaType::User, QuotaType::User) => { assert(a.id == b.id); },
            (QuotaType::Group, QuotaType::Group) => { assert(a.id == b.id); },
            (QuotaType::Project, QuotaType::Project) => { assert(a.id == b.id); },
            _ => { assert(false); },
        }
    }
}
proof fn key_prefix_grows(keys: Seq<Key>, count: int)
    requires 0 <= count < keys.len(),
    ensures forall|key: Key| #[trigger] keys_contain(keys.subrange(0, count + 1), key)
        == (keys_contain(keys.subrange(0, count), key) || rank(keys[count]) == rank(key)),
{
    assert forall|key: Key| keys_contain(keys.subrange(0, count + 1), key)
        == (keys_contain(keys.subrange(0, count), key) || rank(keys[count]) == rank(key)) by {
        if keys_contain(keys.subrange(0, count + 1), key) {
            let at = choose|at: int| 0 <= at < count + 1 && #[trigger] rank(keys.subrange(0, count + 1)[at]) == rank(key);
            if at < count { assert(rank(keys.subrange(0, count)[at]) == rank(key)); }
            else { assert(at == count); }
        }
        if keys_contain(keys.subrange(0, count), key) {
            let at = choose|at: int| 0 <= at < count && rank(keys.subrange(0, count)[at]) == rank(key);
            assert(rank(keys.subrange(0, count + 1)[at]) == rank(key));
        }
        if rank(keys[count]) == rank(key) { assert(rank(keys.subrange(0, count + 1)[count]) == rank(key)); }
    }
}
proof fn subjects_prefix_is_fresh(keys: Seq<Key>, count: int)
    requires subjects_model(keys), 0 <= count < keys.len(),
    ensures !keys_contain(keys.subrange(0, count), keys[count]),
{
    if keys_contain(keys.subrange(0, count), keys[count]) {
        let at = choose|at: int| 0 <= at < count && rank(keys.subrange(0, count)[at]) == rank(keys[count]);
        rank_identifies_key(keys[at], keys[count]);
        assert(keys[at].kind != keys[count].kind);
        assert(false);
    }
}
proof fn sorted_row_key_is_unique(rows: Seq<Snapshot>, a: int, b: int)
    requires sorted(rows), 0 <= a < rows.len(), 0 <= b < rows.len(),
    ensures rank(row_key(rows[a])) == rank(row_key(rows[b])) ==> a == b,
{
    if a < b { assert(rank(row_key(rows[a])) < rank(row_key(rows[b]))); }
    if b < a { assert(rank(row_key(rows[b])) < rank(row_key(rows[a]))); }
}
proof fn publication_push(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>, at: usize, row: Snapshot)
    requires publication_valid(rows, indices, after), indices.len() < 6, at < rows.len(),
        row_valid(row), row.reserved_space == 0, row.reserved_inodes == 0,
        rank(row_key(row)) == rank(row_key(rows[at as int])),
        forall|i: int| 0 <= i < indices.len() ==> indices[i] != at,
    ensures publication_valid(rows, indices.push(at), after.push(row)),
{
    assert forall|i: int, j: int| 0 <= i < j < indices.len() + 1
        implies indices.push(at)[i] != indices.push(at)[j] by {
        if j == indices.len() { assert(indices[i] != at); }
        else { assert(indices[i] != indices[j]); }
    }
}
spec fn account_view(a: Account) -> Snapshot {
    Snapshot { seed: a.seed, reserved_space: a.reserved_space, reserved_inodes: a.reserved_inodes }
}
spec fn account_views(accounts: Seq<Account>) -> Seq<Snapshot> {
    accounts.map(|i: int, a: Account| account_view(a))
}

proof fn account_views_facts(accounts: Seq<Account>)
    ensures account_views(accounts).len() == accounts.len(),
        forall|i: int| 0 <= i < accounts.len()
            ==> #[trigger] account_views(accounts)[i] == account_view(accounts[i]),
{
    reveal(account_views);
}
proof fn account_views_push(accounts: Seq<Account>, account: Account)
    ensures account_views(accounts.push(account)) == account_views(accounts).push(account_view(account)),
{
    account_views_facts(accounts); account_views_facts(accounts.push(account));
    assert(account_views(accounts.push(account)) =~= account_views(accounts).push(account_view(account)));
}
proof fn account_views_update(accounts: Seq<Account>, i: int, account: Account)
    requires 0 <= i < accounts.len(),
    ensures account_views(accounts.update(i, account)) == account_views(accounts).update(i, account_view(account)),
{
    account_views_facts(accounts); account_views_facts(accounts.update(i, account));
    assert(account_views(accounts.update(i, account)) =~= account_views(accounts).update(i, account_view(account)));
}
spec fn account_rank_at(accounts: Seq<Account>, i: int) -> nat {
    rank(row_key(account_view(accounts[i])))
}
proof fn sorted_account_projection(accounts: Seq<Account>)
    requires sorted(account_views(accounts)),
    ensures forall|i: int, j: int| 0 <= i < j < accounts.len()
        ==> #[trigger] account_rank_at(accounts, i) < #[trigger] account_rank_at(accounts, j),
{
    account_views_facts(accounts);
    assert forall|i: int, j: int| 0 <= i < j < accounts.len()
        implies account_rank_at(accounts, i) < account_rank_at(accounts, j) by {
        assert(rank(row_key(account_views(accounts)[i])) < rank(row_key(account_views(accounts)[j])));
    }
}
proof fn ledger_accounts_facts(accounts: Seq<Account>)
    requires ledger_valid(account_views(accounts)),
    ensures accounts.len() <= MAX_ACCOUNTS,
        forall|i: int| 0 <= i < accounts.len() ==> #[trigger] row_valid(account_view(accounts[i]))
            && accounts[i].reserved_space == 0 && accounts[i].reserved_inodes == 0,
        forall|i: int, j: int| 0 <= i < j < accounts.len()
            ==> #[trigger] account_rank_at(accounts, i) < #[trigger] account_rank_at(accounts, j),
{
    account_views_facts(accounts); sorted_account_projection(accounts);
    assert forall|i: int| 0 <= i < accounts.len()
        implies row_valid(account_view(accounts[i])) && accounts[i].reserved_space == 0
            && accounts[i].reserved_inodes == 0 by {
        assert(row_valid(account_views(accounts)[i]));
    }
}
proof fn seed_coverage_push(rows: Seq<Snapshot>, row: Snapshot, seeds: Seq<Seed>, count: int)
    requires 0 <= count < seeds.len(), row.seed == seeds[count],
        forall|k: int| 0 <= k < count ==> rows_contain_seed(rows, seeds[k]),
        forall|j: int| 0 <= j < rows.len() ==> input_contains_seed(seeds.subrange(0, count), rows[j].seed),
    ensures (forall|k: int| 0 <= k <= count ==> #[trigger] rows_contain_seed(rows.push(row), seeds[k])),
        (forall|j: int| 0 <= j < rows.len() + 1
            ==> #[trigger] input_contains_seed(seeds.subrange(0, count + 1), rows.push(row)[j].seed)),
{
    assert forall|k: int| 0 <= k <= count implies rows_contain_seed(rows.push(row), seeds[k]) by {
        if k == count {
            assert(rows.push(row)[rows.len() as int].seed == seeds[k]);
        } else {
            let j = choose|j: int| 0 <= j < rows.len() && rows[j].seed == seeds[k];
            assert(rows.push(row)[j].seed == seeds[k]);
        }
    }
    assert forall|j: int| 0 <= j < rows.len() + 1
        implies input_contains_seed(seeds.subrange(0, count + 1), rows.push(row)[j].seed) by {
        if j == rows.len() {
            assert(seeds.subrange(0, count + 1)[count] == rows.push(row)[j].seed);
        } else {
            let k = choose|k: int| 0 <= k < count && seeds.subrange(0, count)[k] == rows[j].seed;
            assert(seeds.subrange(0, count + 1)[k] == rows.push(row)[j].seed);
        }
    }
}
proof fn seed_coverage_swap(rows: Seq<Snapshot>, seeds: Seq<Seed>, a: int, b: int)
    requires 0 <= a < rows.len(), 0 <= b < rows.len(), a != b,
        forall|j: int| 0 <= j < rows.len() ==> input_contains_seed(seeds, rows[j].seed),
    ensures (forall|seed: Seed| #[trigger] rows_contain_seed(rows.update(a, rows[b]).update(b, rows[a]), seed)
            == rows_contain_seed(rows, seed)),
        (forall|j: int| 0 <= j < rows.len()
            ==> #[trigger] input_contains_seed(seeds, rows.update(a, rows[b]).update(b, rows[a])[j].seed)),
{
    let swapped = rows.update(a, rows[b]).update(b, rows[a]);
    assert forall|seed: Seed| rows_contain_seed(swapped, seed) == rows_contain_seed(rows, seed) by {
        if rows_contain_seed(rows, seed) {
            let old = choose|j: int| 0 <= j < rows.len() && rows[j].seed == seed;
            let at = if old == a { b } else if old == b { a } else { old };
            assert(0 <= at < swapped.len() && swapped[at].seed == seed);
        }
        if rows_contain_seed(swapped, seed) {
            let at = choose|j: int| 0 <= j < swapped.len() && swapped[j].seed == seed;
            let old = if at == a { b } else if at == b { a } else { at };
            assert(0 <= old < rows.len() && rows[old].seed == seed);
        }
    }
    assert forall|j: int| 0 <= j < rows.len()
        implies input_contains_seed(seeds, swapped[j].seed) by {
        let old = if j == a { b } else if j == b { a } else { j };
        assert(swapped[j] == rows[old]);
        assert(input_contains_seed(seeds, rows[old].seed));
    }
}
spec fn insertion_sorted(rows: Seq<Snapshot>, hole: int) -> bool {
    0 <= hole < rows.len()
        && (forall|i: int, j: int| 0 <= i < j < rows.len() && i != hole && j != hole
            ==> rank(row_key(rows[i])) < rank(row_key(rows[j])))
        && (forall|j: int| hole < j < rows.len() ==> rank(row_key(rows[hole])) < rank(row_key(rows[j])))
        && (forall|i: int, j: int| 0 <= i < j < rows.len() ==> rank(row_key(rows[i])) != rank(row_key(rows[j])))
}
proof fn insertion_from_fresh_push(rows: Seq<Snapshot>, row: Snapshot)
    requires sorted(rows),
        forall|i: int| 0 <= i < rows.len() ==> rank(row_key(rows[i])) != rank(row_key(row)),
    ensures insertion_sorted(rows.push(row), rows.len() as int),
{
    assert forall|i: int, j: int| 0 <= i < j < rows.len() + 1
        && i != rows.len() && j != rows.len()
        implies rank(row_key(rows.push(row)[i])) < rank(row_key(rows.push(row)[j])) by {
        assert(j < rows.len());
    }
    assert forall|i: int, j: int| 0 <= i < j < rows.len() + 1
        implies rank(row_key(rows.push(row)[i])) != rank(row_key(rows.push(row)[j])) by {
        if j == rows.len() { assert(rank(row_key(rows[i])) != rank(row_key(row))); }
        else { assert(rank(row_key(rows[i])) < rank(row_key(rows[j]))); }
    }
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

proof fn publication_prefix(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>, count: int)
    requires publication_valid(rows, indices, after), 0 <= count <= indices.len(),
    ensures publication_valid(rows, indices.subrange(0, count), after.subrange(0, count)),
{
}
proof fn updates_have_length(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>)
    requires publication_valid(rows, indices, after),
    ensures apply_updates(rows, indices, after).len() == rows.len(),
    decreases indices.len(),
{
    if indices.len() > 0 {
        publication_prefix(rows, indices, after, indices.len() as int - 1);
        assert(indices.drop_last() =~= indices.subrange(0, indices.len() as int - 1));
        assert(after.drop_last() =~= after.subrange(0, after.len() as int - 1));
        updates_have_length(rows, indices.drop_last(), after.drop_last());
    }
}
proof fn updates_preserve_rank(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>, i: int)
    requires publication_valid(rows, indices, after), 0 <= i < rows.len(),
    ensures apply_updates(rows, indices, after).len() == rows.len(),
        rank(row_key(apply_updates(rows, indices, after)[i])) == rank(row_key(rows[i])),
    decreases indices.len(),
{
    updates_have_length(rows, indices, after);
    if indices.len() > 0 {
        publication_prefix(rows, indices, after, indices.len() as int - 1);
        assert(indices.drop_last() =~= indices.subrange(0, indices.len() as int - 1));
        assert(after.drop_last() =~= after.subrange(0, after.len() as int - 1));
        updates_preserve_rank(rows, indices.drop_last(), after.drop_last(), i);
        if i == indices.last() as int {
            assert(rank(row_key(after.last())) == rank(row_key(rows[i])));
        }
    }
}
proof fn publication_preserves_ledger(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>)
    requires ledger_valid(rows), publication_valid(rows, indices, after),
    ensures ledger_valid(apply_updates(rows, indices, after)),
    decreases indices.len(),
{
    updates_have_length(rows, indices, after);
    if indices.len() > 0 {
        publication_prefix(rows, indices, after, indices.len() as int - 1);
        assert(indices.drop_last() =~= indices.subrange(0, indices.len() as int - 1));
        assert(after.drop_last() =~= after.subrange(0, after.len() as int - 1));
        publication_preserves_ledger(rows, indices.drop_last(), after.drop_last());
        let prior = apply_updates(rows, indices.drop_last(), after.drop_last());
        updates_have_length(rows, indices.drop_last(), after.drop_last());
        let at = indices.last() as int;
        let next = prior.update(at, after.last());
        assert(0 <= at < rows.len());
        assert(row_valid(after.last()) && after.last().reserved_space == 0 && after.last().reserved_inodes == 0);
        assert(rank(row_key(after.last())) == rank(row_key(rows[at])));
        assert forall|i: int| 0 <= i < rows.len()
            implies rank(row_key(next[i])) == rank(row_key(rows[i])) by {
            updates_preserve_rank(rows, indices.drop_last(), after.drop_last(), i);
            if i == at { assert(next[i] == after.last()); }
            else { assert(next[i] == prior[i]); }
        }
        assert forall|i: int, j: int| 0 <= i < j < rows.len()
            implies rank(row_key(next[i])) < rank(row_key(next[j])) by {
            assert(rank(row_key(next[i])) == rank(row_key(rows[i])));
            assert(rank(row_key(next[j])) == rank(row_key(rows[j])));
        }
        assert forall|i: int| 0 <= i < rows.len()
            implies row_valid(next[i]) && next[i].reserved_space == 0 && next[i].reserved_inodes == 0 by {
            if i == at { assert(next[i] == after.last()); }
            else { assert(next[i] == prior[i]); assert(row_valid(prior[i])); }
        }
    }
}
proof fn apply_updates_push(rows: Seq<Snapshot>, indices: Seq<usize>, after: Seq<Snapshot>, at: usize, row: Snapshot)
    requires indices.len() == after.len(), at < rows.len(),
    ensures apply_updates(rows, indices.push(at), after.push(row)) == apply_updates(rows, indices, after).update(at as int, row),
{
    assert(indices.push(at).drop_last() =~= indices);
    assert(after.push(row).drop_last() =~= after);
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
    proof { sorted_account_projection(accounts@); }
    let rank = key_rank(key);
    let mut low = 0usize; let mut high = accounts.len();
    while low < high
        invariant low <= high <= accounts.len(), sorted(account_views(accounts@)),
            rank as nat == crate::quota_reservation::rank(key),
            forall|i: int, j: int| 0 <= i < j < accounts.len() ==> account_rank_at(accounts@, i) < account_rank_at(accounts@, j),
            forall|i: int| 0 <= i < low ==> account_rank_at(accounts@, i) < rank,
            forall|i: int| high <= i < accounts.len() ==> account_rank_at(accounts@, i) >= rank,
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        let current = key_rank(account_key(accounts[mid]));
        if current < rank {
            proof {
                assert forall|i: int| 0 <= i < mid + 1 implies account_rank_at(accounts@, i) < rank by {
                    if i < low { assert(account_rank_at(accounts@, i) < rank); }
                    else if i < mid { assert(account_rank_at(accounts@, i) < account_rank_at(accounts@, mid as int)); }
                    else { assert(i == mid); }
                }
            }
            low = mid + 1;
        } else {
            proof {
                assert forall|i: int| mid <= i < accounts.len() implies account_rank_at(accounts@, i) >= rank by {
                    if i >= high { assert(account_rank_at(accounts@, i) >= rank); }
                    else if mid < i { assert(account_rank_at(accounts@, mid as int) < account_rank_at(accounts@, i)); }
                    else { assert(i == mid); }
                }
            }
            high = mid;
        }
    }
    if low < accounts.len() && key_rank(account_key(accounts[low])) == rank {
        proof {
            assert(crate::quota_reservation::rank(row_key(account_view(accounts@[low as int]))) == rank as nat);
            assert(rank as nat == crate::quota_reservation::rank(key));
        }
        Some(low)
    } else {
        proof {
            assert forall|i: int| 0 <= i < accounts.len() implies account_rank_at(accounts@, i) != rank by {
                if i < low { assert(account_rank_at(accounts@, i) < rank); }
                else {
                    assert(low < accounts.len());
                    if i == low { assert(account_rank_at(accounts@, low as int) != rank); }
                    else { assert(account_rank_at(accounts@, low as int) < account_rank_at(accounts@, i)); }
                }
            }
            assert forall|i: int| 0 <= i < accounts.len()
                implies crate::quota_reservation::rank(row_key(account_view(accounts@[i]))) != crate::quota_reservation::rank(key) by {
                assert(account_rank_at(accounts@, i) != rank);
                reveal(account_rank_at);
            }
        }
        None
    }
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
            let key = account_key(a);
            let found = find(accounts.as_slice(), key);
            if found.is_some() { return None; }
            let ghost old_accounts = accounts@;
            proof {
                account_views_facts(old_accounts);
                ledger_accounts_facts(old_accounts);
                assert forall|k: int| 0 <= k < old_accounts.len()
                    implies rank(row_key(account_views(old_accounts)[k])) != rank(row_key(account_view(a))) by {
                    assert(account_views(old_accounts)[k] == account_view(old_accounts[k]));
                    assert(rank(row_key(account_view(old_accounts[k]))) != rank(key));
                }
                insertion_from_fresh_push(account_views(old_accounts), account_view(a));
                seed_coverage_push(account_views(old_accounts), account_view(a), seeds@, i as int);
            }
            accounts.push(a);
            proof {
                account_views_push(old_accounts, a); account_views_facts(accounts@);
                assert forall|n: int| 0 <= n < accounts.len()
                    implies input_contains_seed(seeds@.subrange(0, i as int + 1), accounts@[n].seed) by {
                    assert(account_views(accounts@)[n] == account_view(accounts@[n]));
                    assert(input_contains_seed(seeds@.subrange(0, i as int + 1), account_views(accounts@)[n].seed));
                }
            }
            let mut j = accounts.len() - 1;
            while j > 0
                invariant j < accounts.len(), accounts.len() == i + 1 <= MAX_ACCOUNTS, i < seeds.len() <= MAX_ACCOUNTS,
                    insertion_sorted(account_views(accounts@), j as int),
                    forall|k: int| 0 <= k < accounts.len() ==> row_valid(account_view(accounts@[k]))
                        && accounts@[k].reserved_space == 0 && accounts@[k].reserved_inodes == 0,
                    (forall|k: int| 0 <= k <= i ==> #[trigger] rows_contain_seed(account_views(accounts@), seeds@[k])),
                    (forall|n: int| 0 <= n < accounts.len() ==> #[trigger] input_contains_seed(seeds@.subrange(0, i as int + 1), accounts@[n].seed)),
                ensures j == 0 || sorted(account_views(accounts@)),
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
                    account_views_facts(before_swap);
                    account_views_update(before_swap, j as int - 1, before_swap[j as int]);
                    account_views_update(before_swap.update(j as int - 1, before_swap[j as int]),
                        j as int, before_swap[j as int - 1]);
                    seed_coverage_swap(account_views(before_swap), seeds@.subrange(0, i as int + 1),
                        j as int - 1, j as int);
                    assert(account_views(accounts@) =~= account_views(before_swap).update(j as int - 1,
                        account_view(before_swap[j as int])).update(j as int, account_view(before_swap[j as int - 1])));
                    account_views_facts(accounts@);
                }
                j -= 1;
            }
            proof {
                if j == 0 { insertion_done(account_views(accounts@), 0); }
                account_views_facts(accounts@);
                assert forall|k: int| 0 <= k < account_views(accounts@).len()
                    implies row_valid(account_views(accounts@)[k])
                        && account_views(accounts@)[k].reserved_space == 0
                        && account_views(accounts@)[k].reserved_inodes == 0 by {
                    assert(account_views(accounts@)[k] == account_view(accounts@[k]));
                }
                assert(ledger_valid(account_views(accounts@)));
            }
            i += 1;
        }
        proof { assert(seeds@.subrange(0, seeds.len() as int) =~= seeds@); account_views_facts(accounts@); }
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
        proof { use_type_invariant(self); account_views_facts(self.accounts@); ledger_accounts_facts(self.accounts@); }
        match find(self.accounts.as_slice(), key) {
            Some(index) => {
                let a = self.accounts[index];
                proof {
                    assert(self.view()[index as int] == account_view(a));
                    assert(row_valid(account_view(a)));
                    assert(exists|i: int| 0 <= i < self.view().len()
                        && self.view()[i] == account_view(a) && rank(row_key(account_view(a))) == rank(key));
                }
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
        proof { use_type_invariant(&self); ledger_accounts_facts(self.accounts@); account_views_facts(self.accounts@); }
        if !subjects_valid(from) || !subjects_valid(to) { return Err((self, Error::DuplicateSubject)); }
        if now == 0 || now > MAX_ACCOUNT { return Err((self, Error::InvalidClock)); }
        if self.epoch == 0xffff_ffff_ffff_ffff { return Err((self, Error::EpochExhausted)); }
        let mut indices = Vec::<usize>::new(); let mut after = Vec::<Account>::new(); let mut i = 0usize;
        while i < from.len()
            invariant i <= from.len() <= 3, indices.len() == after.len() <= 3, indices.len() <= i,
                self.wf(), self.epoch < 0xffff_ffff_ffff_ffff, subjects_model(from@), subjects_model(to@),
                forall|j: int| 0 <= j < self.accounts.len() ==> #[trigger] row_valid(account_view(self.accounts@[j]))
                    && self.accounts@[j].reserved_space == 0 && self.accounts@[j].reserved_inodes == 0,
                self.view().len() == self.accounts.len(),
                forall|j: int| 0 <= j < self.accounts.len() ==> self.view()[j] == account_view(self.accounts@[j]),
                publication_valid(self.view(), indices@, account_views(after@)),
                apply_updates(self.view(), indices@, account_views(after@)).len() == self.view().len(),
                forall|k: int| 0 <= k < indices.len()
                    ==> keys_contain(from@.subrange(0, i as int), row_key(self.view()[indices@[k] as int]))
                        && !keys_contain(to@, row_key(self.view()[indices@[k] as int])),
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
            proof {
                rank_identifies_key(row_key(self.view()[index as int]), from@[i as int]);
                assert(row_key(self.view()[index as int]) == from@[i as int]);
                subjects_prefix_is_fresh(from@, i as int);
                key_prefix_grows(from@, i as int);
            }
            let ghost old_indices = indices@;
            let ghost old_after = after@;
            if !contains(to, from[i]) {
                let mut a = self.accounts[index];
                if a.seed.record.current_space < space || a.seed.record.current_inodes < inodes { return Err((self, Error::Underflow)); }
                a.seed.record.current_space -= space; a.seed.record.current_inodes -= inodes;
                proof { assert(row_valid(account_view(a))); }
                let changed = clear_below_soft(a);
                proof {
                    assert(freed(self.view()[index as int], space, inodes) == Some(account_view(changed)));
                    assert forall|k: int| 0 <= k < old_indices.len() implies old_indices[k] != index by {
                        assert(keys_contain(from@.subrange(0, i as int), row_key(self.view()[old_indices[k] as int])));
                        if old_indices[k] == index { assert(false); }
                    }
                    publication_push(self.view(), old_indices, account_views(old_after), index, account_view(changed));
                    apply_updates_push(self.view(), old_indices, account_views(old_after), index, account_view(changed));
                    account_views_push(old_after, changed);
                }
                indices.push(index); after.push(changed);
            }
            proof {
                updates_have_length(self.view(), indices@, account_views(after@));
                assert forall|j: int| 0 <= j < self.view().len()
                    implies apply_updates(self.view(), indices@, account_views(after@))[j]
                        == if keys_contain(from@.subrange(0, i as int + 1), row_key(self.view()[j]))
                            && !keys_contain(to@, row_key(self.view()[j])) {
                            freed(self.view()[j], space, inodes).unwrap()
                        } else { self.view()[j] } by {
                    sorted_row_key_is_unique(self.view(), j, index as int);
                    if j == index {
                        assert(row_key(self.view()[j]) == from@[i as int]);
                    } else { assert(rank(row_key(self.view()[j])) != rank(from@[i as int])); }
                }
                assert(apply_updates(self.view(), indices@, account_views(after@)) =~=
                    Seq::new(self.view().len(), |j: int|
                        if keys_contain(from@.subrange(0, i as int + 1), row_key(self.view()[j]))
                            && !keys_contain(to@, row_key(self.view()[j])) {
                            freed(self.view()[j], space, inodes).unwrap()
                        } else { self.view()[j] }));
            }
            i += 1;
        }
        proof {
            assert(from@.subrange(0, i as int) =~= from@);
            assert forall|j: int| 0 <= j < self.view().len()
                && keys_contain(from@, row_key(self.view()[j])) && !keys_contain(to@, row_key(self.view()[j]))
                implies freed(self.view()[j], space, inodes).is_some() by {
                assert(keys_contain(from@.subrange(0, i as int), row_key(self.view()[j])));
            }
        }
        proof {
            use_type_invariant(&self);
            ledger_accounts_facts(self.accounts@);
            account_views_facts(self.accounts@);
        }
        i = 0;
        while i < to.len()
            invariant i <= to.len() <= 3, indices.len() == after.len() <= 6, indices.len() <= from.len() + i,
                self.wf(), self.epoch < 0xffff_ffff_ffff_ffff, subjects_model(from@), subjects_model(to@),
                forall|j: int| 0 <= j < self.accounts.len() ==> #[trigger] row_valid(account_view(self.accounts@[j]))
                    && self.accounts@[j].reserved_space == 0 && self.accounts@[j].reserved_inodes == 0,
                self.view().len() == self.accounts.len(),
                forall|j: int| 0 <= j < self.accounts.len() ==> self.view()[j] == account_view(self.accounts@[j]),
                publication_valid(self.view(), indices@, account_views(after@)),
                apply_updates(self.view(), indices@, account_views(after@)).len() == self.view().len(),
                forall|k: int| 0 <= k < indices.len() ==>
                    (keys_contain(from@, row_key(self.view()[indices@[k] as int]))
                        && !keys_contain(to@, row_key(self.view()[indices@[k] as int])))
                    || (!keys_contain(from@, row_key(self.view()[indices@[k] as int]))
                        && keys_contain(to@.subrange(0, i as int), row_key(self.view()[indices@[k] as int]))),
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
            proof {
                rank_identifies_key(row_key(self.view()[index as int]), to@[i as int]);
                assert(row_key(self.view()[index as int]) == to@[i as int]);
                subjects_prefix_is_fresh(to@, i as int);
                key_prefix_grows(to@, i as int);
            }
            let ghost old_indices = indices@;
            let ghost old_after = after@;
            if !contains(from, to[i]) {
                let a = match charge(self.accounts[index], space, inodes, now, false) { Ok(v) => v, Err(e) => { return Err((self, e)); } };
                let a = match finish(a, space, inodes, space, inodes) { Some(v) => v, None => { return Err((self, Error::Arithmetic)); } };
                proof {
                    assert(transferred_row(self.view()[index as int], from@, to@, space, inodes, now) == Some(account_view(a)));
                    assert forall|k: int| 0 <= k < old_indices.len() implies old_indices[k] != index by {
                        if old_indices[k] == index { assert(false); }
                    }
                    publication_push(self.view(), old_indices, account_views(old_after), index, account_view(a));
                    apply_updates_push(self.view(), old_indices, account_views(old_after), index, account_view(a));
                    account_views_push(old_after, a);
                }
                indices.push(index); after.push(a);
            }
            proof {
                updates_have_length(self.view(), indices@, account_views(after@));
                assert forall|j: int| 0 <= j < self.view().len()
                    implies apply_updates(self.view(), indices@, account_views(after@))[j]
                        == if keys_contain(from@, row_key(self.view()[j])) && !keys_contain(to@, row_key(self.view()[j])) {
                            freed(self.view()[j], space, inodes).unwrap()
                        } else if !keys_contain(from@, row_key(self.view()[j]))
                            && keys_contain(to@.subrange(0, i as int + 1), row_key(self.view()[j])) {
                            transferred_row(self.view()[j], from@, to@, space, inodes, now).unwrap()
                        } else { self.view()[j] } by {
                    sorted_row_key_is_unique(self.view(), j, index as int);
                    if j == index { assert(row_key(self.view()[j]) == to@[i as int]); }
                    else { assert(rank(row_key(self.view()[j])) != rank(to@[i as int])); }
                }
            }
            i += 1;
        }
        proof {
            assert(to@.subrange(0, i as int) =~= to@);
            updates_have_length(self.view(), indices@, account_views(after@));
            assert(apply_updates(self.view(), indices@, account_views(after@)) =~=
                transferred_rows(self.view(), from@, to@, space, inodes, now));
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
        proof {
            use_type_invariant(&self);
            account_views_facts(self.staged@);
            assert forall|j: int| 0 <= j < self.staged.len()
                implies row_valid(account_view(self.staged@[j])) by {
                assert(self.staged_view()[j] == account_view(self.staged@[j]));
                assert(row_valid(self.staged_view()[j]));
            }
        }
        if actual_space > self.space || actual_inodes > self.inodes {
            return Err((self.cancel_reservation(), Error::ExceedsReservation));
        }
        let mut after = Vec::<Account>::new(); let mut i = 0usize;
        while i < self.staged.len()
            invariant i <= self.staged.len(), after.len() == i, self.wf(),
                forall|j: int| 0 <= j < self.staged.len() ==> #[trigger] row_valid(account_view(self.staged@[j])),
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
            account_views_facts(self.after@);
        }
        let ghost before = self.before();
        let ghost planned = self.publication();
        let Book { accounts: mut accounts, epoch: original_epoch } = self.book;
        if self.indices.len() != self.after.len() { return Book { accounts, epoch: original_epoch }; }
        let mut i = 0usize;
        // Every defensive check precedes any modification of the plain rows.
        while i < self.indices.len()
            invariant i <= self.indices.len(), self.indices.len() == self.after.len(),
                publication_valid(before, self.indices@, account_views(self.after@)),
                account_views(accounts@) == before, ledger_valid(before),
                planned == apply_updates(before, self.indices@, account_views(self.after@)), ledger_valid(planned),
            decreases self.indices.len() - i,
        {
            if self.indices[i] >= accounts.len() { return Book { accounts, epoch: original_epoch }; }
            let mut j = 0usize;
            while j < i
                invariant j <= i < self.indices.len(), distinct_indices(self.indices@),
                    publication_valid(before, self.indices@, account_views(self.after@)),
                    account_views(accounts@) == before, ledger_valid(before), ledger_valid(planned),
                decreases i - j,
            { if self.indices[j] == self.indices[i] { return Book { accounts, epoch: original_epoch }; } j += 1; }
            i += 1;
        }
        proof { account_views_facts(accounts@); }
        i = 0;
        while i < self.indices.len()
            invariant i <= self.indices.len(), self.indices.len() == self.after.len(),
                publication_valid(before, self.indices@, account_views(self.after@)),
                account_views(accounts@) == apply_updates(before,
                    self.indices@.subrange(0, i as int), account_views(self.after@).subrange(0, i as int)),
                planned == apply_updates(before, self.indices@, account_views(self.after@)), ledger_valid(planned),
                accounts.len() == before.len(),
            decreases self.indices.len() - i,
        {
            let ghost old_accounts = accounts@;
            proof {
                account_views_facts(self.after@);
                account_views_update(old_accounts, self.indices@[i as int] as int, self.after@[i as int]);
                apply_updates_push(before, self.indices@.subrange(0, i as int),
                    account_views(self.after@).subrange(0, i as int), self.indices@[i as int], account_view(self.after@[i as int]));
            }
            accounts[self.indices[i]] = self.after[i];
            proof {
                assert(self.indices@.subrange(0, i as int + 1) =~=
                    self.indices@.subrange(0, i as int).push(self.indices@[i as int]));
                assert(account_views(self.after@).subrange(0, i as int + 1) =~=
                    account_views(self.after@).subrange(0, i as int).push(account_view(self.after@[i as int])));
            }
            i += 1;
        }
        proof {
            assert(self.indices@.subrange(0, self.indices.len() as int) =~= self.indices@);
            assert(account_views(self.after@).subrange(0, self.after.len() as int) =~= account_views(self.after@));
            assert(account_views(accounts@) == planned);
        }
        Book { accounts, epoch: self.epoch }
    }
}

}
