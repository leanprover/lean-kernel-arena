Update the lean4lean arena branches by merging upstream master into them.

Steps:
1. Read `checkers/lean4lean/lean4lean-wrapper.py` to find the current branch names and SHAs in `TOOLCHAIN_TO_TAG`.
2. Clone `https://github.com/nomeata/lean4lean.git` into `_tmp/lean4lean`.
3. Add `https://github.com/digama0/lean4lean.git` as the `upstream` remote and fetch it.
4. For each unique branch in `TOOLCHAIN_TO_TAG` (e.g. `arena/v4.26.0`, `arena/v4.27.0-rc1`):
   - Check out the branch.
   - Merge `upstream/master` into it. If there are conflicts, abort and report them to the user.
   - Push the branch to `origin`.
   - Note the new commit SHA (the short 7-char hash).
5. Update the SHAs in `checkers/lean4lean/lean4lean-wrapper.py` to the new values.
6. Remove `_tmp/lean4lean`.
7. Report the results (old SHA -> new SHA for each branch).
8. Commit the changes to `checkers/lean4lean/lean4lean-wrapper.py`.
