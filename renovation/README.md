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

The project is pinned to the PR release of lean4#16595 (at `8f3431e`). The generator checks
that its kernel accepts every good test and rejects every bad one. Its exporter still writes
format version `3.1.0`, so the generator writes `3.2.0` into the metadata itself.
