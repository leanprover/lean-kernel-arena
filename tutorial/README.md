# Tutorial Test Cases

This directory contains tutorial-style test cases for the Lean kernel arena.
Each declaration in `Tutorial.lean` exercises a specific feature of Lean's type
system, and is exported via `lean4export` as an NDJSON file for external kernel
checkers to process.

A rendered view of the exported test cases, showing the pretty-printed
declarations and their types, is available at:

> <https://arena.lean-lang.org/tutorial/>
