# Kernel Renovation Test Cases

This directory contains small test cases for the kernel renovation
([lean4#14977](https://github.com/leanprover/lean4/issues/14977)).

Most of them are about the per-inductive feature flags that
[lean4#16595](https://github.com/leanprover/lean4/pull/16595) adds to the kernel and to the
export format (version 3.2.0): `isImpredicative`, `isK`, `hasProjections`, `hasEta` and
`hasLargeElim` on each object in `inductive.types` (which no longer has `isReflexive`).
The flags are inputs to the kernel. A checker checks that each flag is allowed for the
declaration and rejects it if not; it must not recompute the flags. Each of these tests
exercises one flag and one of its conditions.

The last ones are about [lean4#15023](https://github.com/leanprover/lean4/pull/15023), which
makes `Quot` live in `Sort (max 1 u)` rather than `Sort u`, so that quotients of propositions
are types. That PR is not in the toolchain of lean4#16595, so the type of `Quot` is replaced
by hand there, and only a kernel with lean4#15023 gets these right.

The tests are written out like the tutorial tests, with the exporter that ships with the
toolchain of lean4#16595.

## Toolchain

The project is pinned to the PR release of lean4#16595 (at `55bd690`). The generator checks
that its kernel accepts every good test and rejects every bad one (for the tests of
lean4#15023: with the replaced `Quot`). Its exporter still writes format version `3.1.0`, so
the generator writes `3.2.0` into the metadata itself.
