<!-- SPDX-License-Identifier: MPL-2.0 -->

# Source-bound indexed-directory admission

The bounded host profile admits Linux DIR_INDEX directories only after checking
the complete source tree, hash ranges, full names, physical allocation and
namespace. This extends immutable inspection and the existing revalidation of
content-write/recovery images. Directory insertion, deletion, splitting,
merging and rebalancing are still unimplemented.

| Design boundary | Implementation and proof | Remaining scope |
| --- | --- | --- |
| Exact source blocks | `directory_htree` collects every logical block through the allocated inode's initialized extent mappings; mapping uniqueness binds each borrowed slice to its exact immutable snapshot range | CortenMM/OSTD frame, cache, lock, BIO and device integration |
| Source configuration | Inode INDEX is directory-only and requires superblock DIR_INDEX; checksum seed uses filesystem seed, inode number and generation; all four superblock hash words and signed/unsigned selection are retained | Keyed SipHash, fscrypt and Unicode casefold |
| Complete structure | `htree_topology` certifies source-selected root/internal children, all leaves, exact claim projection, disjoint roles, no cycles/reuse and no unreferenced supplied blocks | Structural mutations and retirement |
| Hash ranges | `htree_range` derives each child's inherited interval, including odd collision boundaries; checked intervals cannot escape their parents | Split/merge preservation under concurrent mutation |
| Linux routing | Every even hash contained in a checked child interval belongs to the greatest-raw-boundary probe plus matching collision continuations; recursive source-leaf proofs compose these edges | Device/cache execution of lookup traversal |
| Names and absence | `htree_names` checks every live leaf record's hash, retains exact byte names, rejects duplicate full keys, and proves every source leaf record appears in the catalog; a missing key implies complete source absence | Casefold/encrypted names and namespace mutation |
| Namespace projection | `directory_piece` gives roots exactly two dot records, internal nodes no namespace records and leaves the complete canonical record stream; the existing directory index checks target allocation, generation and type | Symlink/special-file types and other directory geometries |
| Whole image | Directory admission carries the full source-bound certificate into existing dot/parent, rootedness, exact/sentinel link-count and global physical ownership checks | Full ext4 admission completeness and mounted VFS operations |

For an edge with raw hash `h`, the child begins at `h & !1`, except that the
first child inherits its parent's lower bound. The next edge bounds the upper
end. An odd next edge includes its base hash in the preceding interval, so a
collision may legitimately occupy both leaves. The final child inherits the
parent's upper end. Checked nested intervals cannot introduce an out-of-parent
hash. Full byte names determine identity; no hash or checksum injectivity is
assumed.

The executable immutable lookup catalog is built by complete traversal. Its
lookup uses the existing full-key `NameSet`, preserving distinct names with an
equal directory hash. The routing proof separately shows that validated source
records lie on the corresponding Linux candidate paths. The implementation
does not claim to perform an on-device binary-search traversal.

The source-bound host adapter is limited to initialized 4 KiB blocks, existing
256-byte extent inodes, at most 4,096 directory blocks and the existing bounded
namespace/allocation profile. The standalone graph allows two additional index
levels when LARGEDIR is selected; whole-filesystem acceptance remains subject
to the explicit feature mask. These resource/format bounds are not full ext4
coverage.

Native validation uses an e2fsck-created indexed directory and checks every
name and target, whole-image namespace admission, correct-checksum leaves moved
across hash ranges, a changed superblock hash seed, an INDEX inode without its
feature bit, two real Linux hash collisions, duplicate names, nested trees,
keyed-hash rejection and canonical root/internal/leaf projections. Rust negative
cases reject forged catalogs/records and mutation of a borrowed source.

All runtime authority stays behind the framekernel boundary. This host library
uses no Linux pages, folios or buffer-head ownership model. Its proofs do not
establish CortenMM ownership, scheduler fairness, hardware persistence or a
mounted filesystem; the corresponding kernel and full-feature gates remain
closed.
