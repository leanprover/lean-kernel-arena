# Lean Kernel Arena

![Lean Kernel Arena Banner](https://raw.githubusercontent.com/leanprover/lean-kernel-arena/refs/heads/master/templates/static/kernel-arena-banner-under-construction.jpg)

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

Using Nix, use `nix develop` obtain a shell that provides the necessary dependencies, which are:

* `python3` with dependencies (`jinja2`, `pyyaml`, `jsonschema`, `markdown`)
* GNU `time`
* `elan` to build Lean code
* `rustc` and `cargo` to build Rust code

### Running Locally

```bash
# Build all tests
./lka.py build-test

# Build all checkers
./lka.py build-checker

# Run all checkers on all tests
./lka.py run-checker

# Generate the website
./lka.py build-site

# View results
python3 -m http.server 8880 --directory _out
```

The `build-test`, `build-checker` and `run-checker` commands can be instructed to build or run specific checkers or tests only.

## Contributing

Contributions are welcome! We especially encourage:

### Contributing Tests

**We need more tests with tricky corner cases!** Tests that expose bugs or edge cases in existing checkers are particularly valuable.

To contribute a test, create a YAML file in the `tests/` directory. Tests can be defined in several ways:

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

See `schemas/test.json` for the complete specification.

### Contributing Checkers

We welcome more alternative kernel implementations, including incomplete ones, especially if they explore a particular corner of the design space (e.g. trimmed for performance, simplicity, verifiability, using a particular term representation, type checking or reduction strategy or a different host langauge).

The book [Type Checking in Lean4](https://ammkrn.github.io/type_checking_in_lean4/) is a good reference on writing a Lean kernel.

To add a new checker implementation:

1. Create a YAML file in the `checkers/` directory
2. Define how to build and run your checker

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
  
  A declined test is simply ignored for the purpose of completeness and correctness. For example, a checker that does not support `native_decide` can decline to process a proof involving the `Lean.trustCompiler axiom`. This is different than rejecting the proof (it may be valid after all) or erroring out (which indicates a bug in the checker).
  
- anything else: an error in the checker

The arena does not automatically update the checkers; please submit new releases manually.

See `schemas/checker.json` for the complete specification.

## Fair Play

Checkers are not run in a sandbox. We assume good faith from all contributors. The goal is to collaboratively improve Lean kernel implementations, not to exploit the test environment. Malicious submissions will be rejected.

## Questions?

Open an issue or discussion on GitHub, or [contact Joachim Breitner on zulip](https://leanprover.zulipchat.com/#narrow/dm/470149-Joachim-Breitner).
