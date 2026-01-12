# Lean Kernel Arena Developer Guide

## Architecture Overview

This is a **benchmarking framework for Lean kernel implementations** that tests proof checkers against standardized test cases and generates comparative reports.

### Core Components
- **`lka.py`**: Single-file CLI tool (884 lines) - main entry point for all operations
- **Test Definitions** (`tests/*.yaml`): Specify Lean export data sources (git repos, modules)
- **Checker Definitions** (`checkers/*.yaml`): Define proof checker build/run commands
- **Templates** (`templates/`): Jinja2 templates for static site generation
- **Nix Environment**: Reproducible Python 3 + dependencies via `flake.nix`

### Data Flow
1. **Tests** → Generate `.ndjson` files with Lean export data in `_build/tests/`
2. **Checkers** → Build executables/scripts in `_build/checkers/`
3. **Results** → Run checkers on tests, save JSON results to `_results/`
4. **Website** → Generate static site in `_out/` with performance comparisons

## Essential Workflows

### Development Commands

If `direnv` is not active, prepend commands with `nix develop -c`.

```bash
./lka.py build-test [name]      # Generate test files from YAML definitions
./lka.py build-checker [name]   # Build checker executables
./lka.py run-checker            # Execute all checkers on all tests
./lka.py build-site             # Generate website from results
```

### Key Conventions
- **Exit codes determine status**: 0=accepted, 1=rejected, 2=declined
- **YAML-driven configuration**: Tests and checkers defined in separate YAML files
- **Name derivation**: File stem becomes the entity name (no explicit `name` field needed)
- **Stats tracking**: File sizes, line counts with SI prefixes (5.6M lines, 290.7 MB)

### Configuration Schema
- **Test configurations**: See `schemas/test.json` for complete YAML validation schema
- **Checker configurations**: See `schemas/checker.json` for complete YAML validation schema
- **Schema validation**: Enforced automatically with helpful error messages
- **Common patterns**: Git repositories, local directories, module exports via lean4export

### Result Data Structure
Results stored as `_results/{checker}_{test}.json`:
```json
{
  "checker": "checker-name",
  "test": "test-name", 
  "status": "accepted|rejected|declined|error",
  "exit_code": 0,
  "wall_time": 1.23,
  "cpu_time": 1.18,
  "max_rss": 1048576,
  "stdout": "...",
  "stderr": "..."
}
```

### Template Architecture
- **Base template inheritance**: `base.html` → `index.html`, `checker.html`
- **Chota CSS framework**: Minimal, responsive styling
- **Per-checker pages**: URL structure `checker/{name}/index.html`
- **Collapsible details**: Test YAML definitions in `<details>` elements

## Critical Integration Points

### Lean4Export Dependency
Tests using `module` or `leanfile` fields auto-clone and build `lean4export` tool from GitHub. Multiple lean4export builds are cached per toolchain in `_build/lean4export/{toolchain}/` directories, allowing tests with different Lean versions to coexist.

### File System Layout
```
_build/tests/{name}.ndjson        # Generated test data
_build/tests/{name}.stats.json    # File size/line count metadata  
_build/lean4export/{toolchain}/   # Per-toolchain lean4export builds
_build/checkers/{name}/           # Checker build directories
_results/{checker}_{test}.json    # Individual run results
_out/                             # Generated website
```

### GitHub Actions Integration
- Manual trigger workflow: `build-and-deploy.yml`
- Nix environment setup via `cachix/install-nix-action`
- GitHub Pages deployment from `_out/` directory

## Project-Specific Patterns

### Verbose Mode Implementation
Global `VERBOSE` flag enables command tracing via `run_cmd()` helper with timing stats.

### Template Data Binding
Checker pages receive enriched data: YAML source, test stats, result details with color-coded status badges.

### Error Handling Strategy
- Functions return boolean success/failure
- Commands continue on individual failures, report summary counts
- Missing test files handled gracefully (status: "error")

## Development Workflow

### Task Completion Protocol
**Always commit changes after completing each task or logical unit of work:**
```bash
git add .
git commit -m "Brief description of changes made"
```

This ensures:
- Progress is preserved between AI agent sessions
- Changes can be easily reviewed and reverted if needed
- Development history remains clean and traceable
- Collaboration with human developers is seamless