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

The others are about the other changes of the renovation: complete comparison of universe
levels, eta for unit-like types (lean4#15372), for the major premise of a recursor
(lean4#15371) and for partial applications of constructors and recursors (lean4#15373,
lean4#15374), and `Quot` living in `Sort (max 1 u)` rather than `Sort u`
([lean4#15023](https://github.com/leanprover/lean4/pull/15023)), so that quotients of
propositions are types.

Some of these changes are not in the toolchain of lean4#16595 yet. The good tests of complete
level comparison and of lean4#15372 are added without the kernel checking them
(`ahead_good_thm`, `levelEqTest`, `levelLeTest`), and warn once the kernel accepts them. Only a
kernel with these changes gets them right.

The tests are written out like the tutorial tests, with the exporter that ships with the
toolchain of lean4#16595.

## Toolchain

The project is pinned to the PR release of lean4#16595 (at `a8ad4db`). The generator checks
that its kernel accepts every good test (except those ahead of it) and rejects every bad one.
