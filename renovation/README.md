# Kernel Renovation Test Cases

This directory contains small test cases for the per-inductive feature flags that
[lean4#16595](https://github.com/leanprover/lean4/pull/16595) adds to the kernel and to the
export format (version 3.2.0): `isImpredicative`, `isK`, `hasProjections`, `hasEta` and
`hasLargeElim` on each object in `inductive.types`.

The flags are inputs to the kernel. A checker checks that each flag is allowed for the
declaration and rejects it if not; it must not recompute the flags. Each test in
`Renovation.lean` exercises one flag and one of its conditions. The tests are written out
like the tutorial tests, with the exporter that ships with the toolchain of the PR.

All checkers decline these tests for now (see `declines` in `checkers/*.yaml`); remove
`renovation` from that list to opt in.

## Toolchain

The project is pinned to the PR release of lean4#16595 at `53e1623`, the newest one
available, which predates the final version of the PR in two ways that matter here:

* It still generates reduction rules for recursors without large elimination. The test
  generator drops them (`dropSmallRecRules` in `Renovation/Meta.lean`), so the exports are as
  with the final version.
* It does not check that only the first type of a mutual block is marked `isK`, so the
  generator only warns about `KMutSecondB` rather than failing.

With these two workarounds, the exports are identical to those of a toolchain built from the
PR at `0729164`, on which every good test is accepted and every bad test is rejected by the
kernel. Once there is a PR release (or a release) with the final version, bump
`lean-toolchain` and drop the workarounds.
