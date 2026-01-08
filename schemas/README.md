# YAML Configuration Schemas

This directory contains JSON Schema files that define and validate the structure of YAML configuration files used in the Lean Kernel Arena.

## Schema Files

### test.json
Validates test configuration files in the `tests/` directory.

**Supported test patterns:**
1. **Git repository with run command** - Clone a repo and run a custom command
   - Required: `url`, `run`
   - Optional: `ref`, `rev`, `pre-build`, `outcome`
   
2. **Git repository with module export** - Clone a repo and export a Lean module
   - Required: `url`, `module`
   - Optional: `ref`, `rev`, `pre-build`, `outcome`
   
3. **Static file** - Use an existing file as test data
   - Required: `file`
   - Optional: `outcome`
   
4. **Local directory with run command** - Use local directory and run command
   - Required: `dir`, `run`
   - Optional: `pre-build`, `outcome`
   
5. **Local directory with module export** - Use local directory and export module
   - Required: `dir`, `module`
   - Optional: `pre-build`, `outcome`

### checker.json
Validates checker configuration files in the `checkers/` directory.

**Supported checker patterns:**
1. **Git repository checker** - Clone a repo and build/run checker
   - Required: `url`, `run`
   - Optional: `version`, `ref`, `rev`, `build`
   
2. **Local directory checker** - Use local directory source
   - Required: `dir`, `run`
   - Optional: `version`, `build`
   
3. **Simple checker** - Just a run command, optionally with build step
   - Required: `run`
   - Optional: `version`, `build`

## Field Definitions

### Common Fields
- `url`: Git repository URL (must be valid URI)
- `ref`: Git branch or tag name
- `rev`: Git commit hash (7-40 hex characters)
- `dir`: Local directory path (relative to project root for tests, relative to `checkers/` for checkers)
- `version`: Version identifier string

### Test-Specific Fields
- `file`: Static file path relative to project root
- `module`: Lean module name to export using lean4export
- `run`: Shell command to generate test data (`$OUT` variable available)
- `pre-build`: Command to run before building (e.g., `lake exe cache get`)
- `outcome`: Expected test result (`"accept"` or `"reject"`)

### Checker-Specific Fields
- `build`: Shell command to build the checker (optional - only needed if compilation is required)
- `run`: Shell command to run the checker (`$IN` variable points to input file)

## Validation

Schema validation is automatically performed when loading YAML files. Validation errors will show:
- The file path with the error
- The specific field path where validation failed
- A description of what was expected vs. what was found

## JSON Schema Standard

These schemas use JSON Schema Draft 07 specification. They can be used with any JSON Schema validator, not just the Python implementation in this project.

**Useful tools for schema development:**
- [JSON Schema validator online](https://www.jsonschemavalidator.net/)
- [JSON Schema documentation](https://json-schema.org/)
- VS Code JSON Schema extension for syntax highlighting and validation