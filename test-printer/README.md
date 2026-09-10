# test-printer

A Lean 4 CLI tool that reads tutorial test files (exported via `lean4export` as
NDJSON) and produces an interactive HTML page showing each test's declarations,
types, and values.

## Usage

```
lake exe test-printer [--pp-all] <test-dir> <output-path>
```

- `<test-dir>`: Directory containing `good/` and `bad/` subdirectories with
  `.ndjson`, `.info.json`, and `.stats.json` files.
- `<output-path>`: Path to write the generated HTML file.
- `--pp-all`: Show all declarations, not just those new to each test.

## Building

```
cd test-printer
lake build
```

## Features

- Standalone expression pretty-printer with width-aware line wrapping
- Declaration merging across tests: shared declarations shown as "Includes" links
- Sidebar navigation with scroll-based highlighting
- Mobile-friendly layout with toggleable sidebar
- Markdown descriptions rendered via md4lean (cmark bindings)
