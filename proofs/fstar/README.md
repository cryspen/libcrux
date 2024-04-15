# Extraction directories
The `extraction` directory is generated automatically by hax from the
Rust code. The `extraction-edited` and `extraction-secret-independent`
are hand-edited snapshots of `extraction` at some point in time.

The edits (1) on the one hand between `extraction` and
`extraction-edited` and (2) on the other hand between
`extraction-edited` and `extraction-secret-independent` are tracked
via diff files.

Whenever the rust code changes, the extracted F* code in `extraction`
changes as well. The CI then applies the diff files: if the patch
process fails or if the resulting patched F* doesn't typecheck, the CI
fails.

The bash script `./patches.sh` takes care of the diffs:
 - `./patches.sh create` creates patches out of the `extraction*` folders;
 - `./patches.sh apply` drops the `extraction-edited` and
   `extraction-secret-independent` folders and re-creates them out of
   the `extraction-edited.patch` and
   `extraction-secret-independent.patch` files.

# Workflow
Ideally:
 - since `extraction` is a projection from the Rust code via the hax
   toolchain, we should not commit it in the repository;
 - since `extraction-edited` and `extraction-secret-independent` are
   created via the diff files, we should not commit them either in the
   repository.

Currently, we do check those 3 folders in. Thus, when we change
anything in the F* proofs, we should always make sure we keep the diff
files and those folder in a coherent state.

In other words, this means that the last commit of each PR should be
about regeneration of diff files (using the command `./patches.sh
create`) and regeneration of the `extraction` folder.
