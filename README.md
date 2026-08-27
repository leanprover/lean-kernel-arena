# Lean Kernel Arena

![Lean Kernel Arena Banner](https://raw.githubusercontent.com/leanprover/lean-kernel-arena/refs/heads/master/templates/static/kernel-arena-banner.jpg)

A benchmarking framework for Lean kernel implementations that tests proof checkers against standardized test cases and generates comparative reports.

**<https://arena.lean-lang.org>**

## Overview

The Lean Kernel Arena provides a systematic way to:

- **Advertise** different Lean kernel implementations
- **Test** them for completeness and soundness
- **Benchmark** their performance on real-world proofs
- **Identify** edge cases and potential bugs in proof checkers
- **Facilitate** new kernel development, by providing a sequence of more interesting test cases

## Architecture

The framework consists of:

- **Test definitions** (`tests/*.yaml`): Specify Lean export data sources and expected outcomes
- **Checker definitions** (`checkers/*.yaml`): Define proof checker build and run commands
- A **CLI tool** (`lka.py`) to orchestrate everything and produce a static site

## Getting Started

### Development Environment

The arena tool (`lka.py`) has a number of dependencies, which include:

* `elan` to build Lean code
* `rustc` and `cargo` to build Rust code
* GNU `time`

as well as a Python installation with a number of Python dependencies.

Using Nix, you can use `nix develop` to obtain a shell that provides all of the necessary dependencies.

### Running Locally

#### Via `uv`

After [installing `uv`](https://docs.astral.sh/uv/#installation) and the 3 non-Python dependencies above, you can use:

```bash
# Build all tests
uv run lka.py build-test

# Build all checkers
uv run lka.py build-checker

# Run all checkers on all tests
uv run lka.py run

# Generate the website
uv run lka.py build-site

# View results
python3 -m http.server 8880 --directory _out
```

where all commands will automatically install any requisite Python dependencies.

The `build-test`, `build-checker` and `run` commands can be instructed to build or run specific checkers or tests only.

#### Via a Virtual Environment With Python Dependencies Installed

If you have installed the Python dependencies yourself, or via `nix`:

```bash
# Build all tests
./lka.py build-test

# Build all checkers
./lka.py build-checker

# Run all checkers on all tests
./lka.py run

# Generate the website
./lka.py build-site

# View results
python3 -m http.server 8880 --directory _out
```

## Contributing

Contributions are welcome! We especially encourage:

### Contributing Tests

**We need more tests with tricky corner cases!** Tests that expose bugs or edge cases in existing checkers are particularly valuable.

To contribute a test, create a YAML file in the `tests/` directory.  See `schemas/test.json` for the complete specification.  Tests can be defined in several ways:


#### Module-based test (from a Lean repository)
```yaml
description: |
  Your test description here
url: https://github.com/user/lean-project
ref: main        # git branch or tag
rev: deadbeeef   # git revision
module: MyModule # module to export
outcome: accept  # or 'reject' for tests that should fail
export-decls:   # optional: export only specific declarations and their dependencies
  - myTheorem

```

#### Single file test

When a full lake project is overkill and a single file suffices, use `leanfile`:

```yaml
description: |
  Test for a specific corner case
leanfile: tests/my-test.lean
outcome: accept
export-decls:   # optional: export only specific declarations and their dependencies
  - myTheorem
```

#### Static export file

For a hand-crafted export file, use `file`.

```yaml
description: |
  Pre-generated export data
file: tests/my-export.ndjson
outcome: reject
```

#### Multiple test generation

For advanced use cases where you want to generate many test cases from a single source, use `multiple: true`. This is only valid with the `run` field and generates multiple `.ndjson` files organized into `good/` and `bad/` subdirectories:

```yaml
description: |
  Generate multiple test cases from a Lean project
dir: my-test-project  # or use url/ref/rev for git repos
multiple: true
run: |
  lake clean
  lake build MyProject
```

Your `run` command should generate test files in the direcory `$OUT`, as either `good/<name>.ndjson` or `bad/<name>.ndjson`.  You can put a `<name>.info.json` file next to it with a `{"description": "…"}`.

This approach is useful for systematic testing across many related scenarios or when implementing tutorial-style test suites.

### Contributing Checkers

We welcome more alternative kernel implementations, including incomplete ones, especially if they explore a particular corner of the design space (e.g. trimmed for performance, simplicity, verifiability, using a particular term representation, type checking or reduction strategy or a different host langauge).

The following resources may be useful:

* The thesis [The Type Theory of Lean](https://github.com/digama0/lean-type-theory/releases) by Mario Carneiro is a thorough description of Lean's theory.
* The book [Type Checking in Lean4](https://ammkrn.github.io/type_checking_in_lean4/) by Chris Bailey has good advice on on writing a Lean kernel.
* On the [arena website](https://arena.lean-lang.org/) you can download a zipfile with the arena tests (excluding large ones).
* The arena website also publishes a machine-readable `results.json` with all checker metadata, test metadata and individual results, useful for further analysis.
* The [source of the tutorial tests](https://github.com/leanprover/lean-kernel-arena/blob/master/tutorial/Tutorial.lean) suggests a sequence in which to implement tests.

To add a new checker implementation:

1. Create a YAML file in the `checkers/` directory.
2. Define how to build and run your checker
   See `schemas/checker.json` for the complete specification.

Example:

```yaml
description: |
  Description of your checker implementation
version: "1.0.0"
url: https://github.com/user/my-checker
ref: main        # git branch or tag
rev: deadbeef    # git revision
build: cargo build --release
run: ./target/release/my-checker < $IN
```

The `run` command receives the test file path via the `$IN` environment variable, in the NDJSON-based format created by [`lean4export`](https://github.com/leanprover/lean4export). (At the time of writing, the [format is still in flux](https://github.com/leanprover/lean4export/issues/3).)

**Exit codes:**

- `0`: Proof accepted (valid)
- `1`: Proof rejected (invalid)
- `2`: Declined (checker cannot handle this proof)
  
  A declined test is simply ignored for the purpose of completeness and correctness. For example, a checker that does not support `native_decide` can decline to process a proof involving the `Lean.trustCompiler` axiom. This is different from rejecting the proof (you are not claiming that the proof is not valid) or erroring out (which indicates a bug in the checker).
  
- anything else: an error in the checker

If it is already known that a checker cannot handle a test, and running it would just waste time, the checker YAML can list that test in the `declines` field (a test name or list of test names). Such tests are recorded as declined without running the checker at all.

The arena does not automatically update the checkers; please submit new releases manually.

## Rounds

The arena runs in **rounds**. <https://arena.lean-lang.org> shows the round
currently in progress, rebuilt whenever checkers or tests change. Closing a
round archives it unchanged under
<https://arena.lean-lang.org/round/>, so that results stay
referenceable even as checkers, tests and the Lean version they are measured
against move on.

Rounds are named after a year and a month, e.g. `2026-10`, but are closed
whenever it seems right rather than on a schedule.

### Closing a round

Push a tag `round-<name>`:

```bash
git tag round-2026-10
git push origin round-2026-10
```

This runs the full CI build (no tests are skipped), and then:

1. reserves a DOI on Zenodo,
2. builds the site with the round name and DOI baked in,
3. creates the GitHub release `round-2026-10` with three assets, each named
   after the round: the whole site as `lean-arena-round-2026-10-site.tar.gz`,
   the raw results as `lean-arena-round-2026-10-results.json`, and the test
   suite as `lean-arena-round-2026-10-tests.tar.gz`,
4. uploads those to Zenodo as a draft deposition,
5. reassembles `/round/` from all round releases and deploys the site,
6. publishes the Zenodo record, which mints the DOI.

Publishing cannot be undone, so it happens last, once everything else has
succeeded. If an earlier step fails, the draft deposition is discarded again
and no DOI is minted.

Each round is deposited as a new version of the previous one, so all rounds
share a concept DOI that resolves to the most recent round, next to their
individual per-round DOIs. The deposition id needed for this is recorded in
each round's own `results.json`.

### Trying it out

A tag `test-round-<name>` runs exactly the same thing, but against
[sandbox.zenodo.org](https://sandbox.zenodo.org) and without deploying the
site. Delete the tag and the GitHub release afterwards and nothing remains.
The tag does not have to be on `master`, so a change to the round machinery
can be exercised end to end while it is still a pull request.

CI needs two secrets: `ZENODO_TOKEN` and `ZENODO_SANDBOX_TOKEN`, each a
personal access token with the `deposit:write` and `deposit:actions` scopes,
from zenodo.org and sandbox.zenodo.org respectively.

The deposition metadata (authors, license, keywords) lives in
[`.zenodo.json`](.zenodo.json); title, version and publication date are filled
in per round.

## Fair Play

Checkers are not run in a sandbox. We assume good faith from all contributors. The goal is to collaboratively improve Lean kernel implementations, not to exploit the test environment. Malicious submissions will be rejected.

## On `Init.Prelude`

The official Lean kernel assumes that `Init.Prelude` is **the* prelude shipped with Lean, and does not support other declarations here. Therefore the tests in the arena satisfy that declarations from `Init.Prelude` are either completely absent, or come from an official release or release candidate. The lean version in the test header can be used to recognize the version, should that be useful to some checker. Checkers are free to do additional checks on these declarations, but are not expected to accept or reject declarations that are not part of an official release.

Some checkers perform extra checks here. If there is interest in testing this functionality, we can label such tests and let the official kernel decline handling them.

## Questions?

Open an issue or discussion on GitHub, or [contact Joachim Breitner on zulip](https://leanprover.zulipchat.com/#narrow/dm/470149-Joachim-Breitner).
