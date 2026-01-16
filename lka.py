#!/usr/bin/env python3
"""Lean Kernel Arena - Tool for managing Lean kernel tests and checkers."""

import argparse
import datetime
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import yaml
import jsonschema
import markdown
from jinja2 import Environment, FileSystemLoader, select_autoescape
import shlex

# Global verbose flag
VERBOSE = False

# Timing/measurement utilities


def get_project_root() -> Path:
    """Get the project root directory."""
    return Path(__file__).parent.resolve()


def load_schema(schema_name: str) -> dict:
    """Load a JSON schema file."""
    schema_file = get_project_root() / "schemas" / f"{schema_name}.json"
    if not schema_file.exists():
        raise FileNotFoundError(f"Schema file not found: {schema_file}")
    with open(schema_file, "r") as f:
        return json.load(f)


def validate_yaml_data(data: dict, schema_name: str, file_path: Path) -> None:
    """Validate YAML data against a schema."""
    try:
        schema = load_schema(schema_name)
        jsonschema.validate(data, schema)
    except jsonschema.ValidationError as e:
        # Format a helpful error message
        error_path = " -> ".join(str(p) for p in e.absolute_path) if e.absolute_path else "root"
        print(f"Schema validation error in {file_path}:")
        print(f"  Path: {error_path}")
        print(f"  Error: {e.message}")
        if e.validator_value:
            print(f"  Expected: {e.validator_value}")
        if hasattr(e, 'instance') and e.instance is not None:
            print(f"  Found: {e.instance}")
        sys.exit(1)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        sys.exit(1)


def format_duration(seconds: float) -> str:
    """Format a duration in seconds to a human-readable string."""
    if seconds >= 3600:
        return f"{seconds / 3600:.1f}\u202fh"
    elif seconds >= 60:
        return f"{seconds / 60:.1f}\u202fm"
    elif seconds >= 1:
        return f"{seconds:.1f}\u202fs"
    else:
        return f"{seconds * 1000:.0f}\u202fms"


def format_memory(bytes_value: float) -> str:
    """Format memory usage in bytes to a human-readable string."""
    if bytes_value >= 1024 * 1024 * 1024:
        return f"{bytes_value / (1024 * 1024 * 1024):.1f}\u202fGB"
    elif bytes_value >= 1024 * 1024:
        return f"{bytes_value / (1024 * 1024):.1f}\u202fMB"
    elif bytes_value >= 1024:
        return f"{bytes_value / 1024:.1f}\u202fKB"
    else:
        return f"{bytes_value:.0f}\u202fB"


def render_markdown(text: str) -> str:
    """Render markdown text to HTML."""
    if not text:
        return ""
    
    # Configure markdown with extensions for better HTML output
    md = markdown.Markdown(extensions=['extra', 'codehilite', 'toc'])
    return md.convert(text.strip())


def measure_perf_with_fallback(
    cmd: str | list[str],
    cwd: Path | None = None,
    env: dict | None = None,
    shell: bool = False,
    capture_output: bool = True,
) -> tuple[subprocess.CompletedProcess, dict]:
    """Run a command and measure performance metrics, with fallback if GNU time is unavailable.
    
    Returns:
        Tuple of (subprocess result, metrics dict)
        
    Metrics dict contains:
    - wall_time: Wall clock time in seconds
    - cpu_time: CPU time in seconds (measured via GNU time or derived from rusage)
    - max_rss: Maximum RSS in bytes
    """
    # Record wall time manually as fallback
    start_wall_time = time.time()
    
    # Try to use GNU `time` if available for structured measurements
    metrics = {}
    use_gnu_time = False
    try:
        time_check = subprocess.run(["time", "--version"], capture_output=True, timeout=2)
        if time_check.returncode == 0:
            use_gnu_time = True
    except (FileNotFoundError, subprocess.TimeoutExpired):
        use_gnu_time = False

    if use_gnu_time:
        # Use GNU time to collect real/user/sys and max RSS
        with tempfile.NamedTemporaryFile(mode='w+', delete=False) as tmp:
            tmp_path = tmp.name

        # Format string that GNU time understands
        fmt = "real_seconds=%e\nuser_seconds=%U\nsys_seconds=%S\nmax_rss_kb=%M"

        try:
            if isinstance(cmd, list):
                time_cmd = ["time", "-f", fmt, "-o", tmp_path, "--", *cmd]
            else:
                # When shell=True we need to run via sh -c
                if shell:
                    time_cmd = ["time", "-f", fmt, "-o", tmp_path, "--", "sh", "-c", cmd]
                else:
                    time_cmd = ["time", "-f", fmt, "-o", tmp_path, "--"] + cmd.split()

            result = subprocess.run(
                time_cmd,
                cwd=cwd,
                env=(env or os.environ).copy(),
                shell=False,
                capture_output=capture_output,
                text=True,
            )

            # Read metrics from tmp file
            time_metrics = {}
            try:
                with open(tmp_path, 'r') as f:
                    for line in f:
                        line = line.strip()
                        if not line:
                            continue
                        if '=' in line:
                            k, v = line.split('=', 1)
                            time_metrics[k.strip()] = v.strip()
            except Exception:
                pass
            finally:
                try:
                    os.unlink(tmp_path)
                except Exception:
                    pass

            # Fill metrics with sensible fallbacks
            try:
                metrics["wall_time"] = float(time_metrics.get("real_seconds", time.time() - start_wall_time))
            except Exception:
                metrics["wall_time"] = time.time() - start_wall_time

            try:
                user_s = float(time_metrics.get("user_seconds", "0"))
                sys_s = float(time_metrics.get("sys_seconds", "0"))
                metrics["cpu_time"] = user_s + sys_s
            except Exception:
                metrics["cpu_time"] = 0.0

            try:
                max_rss_kb = int(time_metrics.get("max_rss_kb", "0"))
                metrics["max_rss"] = max_rss_kb * 1024
            except Exception:
                metrics["max_rss"] = 0.0

        except Exception:
            # If GNU time fails for any reason, run normally and fall back
            result = subprocess.run(
                cmd,
                cwd=cwd,
                env=env,
                shell=shell,
                capture_output=capture_output,
                text=True,
            )
            metrics["wall_time"] = time.time() - start_wall_time
            metrics["cpu_time"] = 0.0
            metrics["max_rss"] = 0.0
    else:
        # Fallback: run normally and measure wall time
        result = subprocess.run(
            cmd,
            cwd=cwd,
            env=env,
            shell=shell,
            capture_output=capture_output,
            text=True,
        )
        metrics["wall_time"] = time.time() - start_wall_time
        metrics["cpu_time"] = 0.0  # Not measured here (no GNU time available)
        metrics["max_rss"] = 0.0
    
    return result, metrics


def run_cmd(
    cmd: str | list[str],
    cwd: Path | None = None,
    env: dict | None = None,
    shell: bool = False,
    capture_output: bool = True,
    measure_perf: bool = False,
) -> subprocess.CompletedProcess:
    """Run a command with optional verbose output and performance measurement.
    
    Args:
        cmd: Command to run (string for shell=True, list for shell=False)
        cwd: Working directory
        env: Environment variables
        shell: Whether to run as shell command
        capture_output: Whether to capture stdout/stderr
        measure_perf: Whether to measure detailed performance metrics
    
    Returns:
        CompletedProcess instance with additional attributes:
        - wall_time: Wall clock time in seconds
        - cpu_time: CPU time in seconds (if available)
        - max_rss: Maximum RSS in bytes (if available)
    """
    global VERBOSE
    
    # Format command for display
    if isinstance(cmd, list):
        cmd_str = " ".join(cmd)
    else:
        cmd_str = cmd
    
    if VERBOSE:
        cwd_str = f" (in {cwd})" if cwd else ""
        print(f"    $ {cmd_str}{cwd_str}")
    
    if measure_perf:
        # Use detailed performance measurement
        result, metrics = measure_perf_with_fallback(
            cmd, cwd=cwd, env=env, shell=shell, capture_output=capture_output
        )
        
        # Add metrics as attributes to the result
        result.wall_time = metrics["wall_time"]
        result.cpu_time = metrics["cpu_time"]
        result.max_rss = metrics["max_rss"]
        
        if VERBOSE:
            status = "ok" if result.returncode == 0 else f"FAILED (exit {result.returncode})"
            metrics_str = f"wall: {format_duration(result.wall_time)}"
            metrics_str += f", cpu: {format_duration(result.cpu_time)}"
            metrics_str += f", rss: {format_memory(result.max_rss)}"
            print(f"      -> {status} ({metrics_str})")
    else:
        # Use simple timing
        start_time = time.time()
        
        result = subprocess.run(
            cmd,
            cwd=cwd,
            env=env,
            shell=shell,
            capture_output=capture_output,
            text=True,
        )
        
        elapsed = time.time() - start_time
        
        # Add basic timing as attributes
        result.wall_time = elapsed
        result.cpu_time = 0.0  # Not measured
        result.max_rss = 0.0   # Not measured
        
        if VERBOSE:
            status = "ok" if result.returncode == 0 else f"FAILED (exit {result.returncode})"
            print(f"      -> {status} in {format_duration(elapsed)}")
    
    return result


def get_lean_toolchain(directory: Path) -> str | None:
    """Read the lean-toolchain file from a directory and return the toolchain string.
    
    Args:
        directory: Directory to look for lean-toolchain file
        
    Returns:
        Toolchain string (e.g., 'leanprover/lean4:v4.27.0-rc1'), or None if not found
    """
    toolchain_file = directory / "lean-toolchain"
    if toolchain_file.exists():
        try:
            with open(toolchain_file, "r") as f:
                return f.read().strip()
        except Exception as e:
            print(f"  Warning: Could not read {toolchain_file}: {e}")
    return None


def run_lean4export(lean4export_dir: Path, module_name: str, export_decls: list | None, cwd: Path, out_file: Path) -> bool:
    """Run lean4export (via lake env) to export a module.

    lean4export_dir: path to the checked-out/build lean4export repo
    module_name: module name to export
    export_decls: optional list of declaration names to pass after --
    cwd: working directory to run lake env from
    out_file: output path for NDJSON
    """
    lean4export_bin = lean4export_dir / ".lake" / "build" / "bin" / "lean4export"
    if not lean4export_bin.exists():
        print(f"  Error: lean4export binary not found at {lean4export_bin}")
        return False

    # Build command
    cmd = f"lake env {lean4export_bin} {module_name}"
    if export_decls:
        # Quote each decl for shell safety
        decls = " ".join(shlex.quote(str(d)) for d in export_decls)
        cmd += f" -- {decls}"
    cmd += f" > {out_file}"

    result = run_cmd(cmd, cwd=cwd, shell=True)
    if result.returncode != 0:
        print(f"  Export failed: {result.stderr}")
        return False
    return True


def setup_lean4export(toolchain: str) -> Path | None:
    """Clone and build lean4export for a specific Lean toolchain.
    
    Args:
        toolchain: Lean toolchain string (e.g., 'leanprover/lean4:v4.27.0-rc1')
        
    Returns:
        Path to lean4export directory for this toolchain, or None on failure
        
    Note: Failed temporary directories are left in place for debugging purposes.
    """
    # Sanitize toolchain string for use in file paths
    toolchain_dir_name = toolchain.replace("/", "_").replace(":", "_")
    build_base_dir = get_project_root() / "_build"
    lean4export_dir = build_base_dir / "lean4export" / toolchain_dir_name
    
    if not lean4export_dir.exists():
        print(f"  Cloning lean4export for toolchain {toolchain}...")
        
        # Work in temporary directory first
        lean4export_tmp_dir = Path(str(lean4export_dir) + ".tmp")
        
        # Clean up any existing temporary directory
        if lean4export_tmp_dir.exists():
            shutil.rmtree(lean4export_tmp_dir)
        
        lean4export_tmp_dir.mkdir(parents=True, exist_ok=True)
        
        clone_cmd = ["git", "clone", "--branch", "arena_json_output",
                    "https://github.com/leanprover/lean4export",
                    str(lean4export_tmp_dir)]
        result = run_cmd(clone_cmd)
        if result.returncode != 0:
            print(f"  Error cloning lean4export: {result.stderr}")
            return None

        # Set the specific toolchain
        toolchain_file = lean4export_tmp_dir / "lean-toolchain"
        try:
            with open(toolchain_file, "w") as f:
                f.write(toolchain + "\n")
        except Exception as e:
            print(f"  Error writing lean-toolchain file: {e}")
            return None

        print(f"  Building lean4export with toolchain {toolchain}...")
        result = run_cmd("lake build", cwd=lean4export_tmp_dir, shell=True)
        if result.returncode != 0:
            print(f"  Error building lean4export: {result.stderr}")
            return None
        
        # Move temporary directory to final location atomically
        try:
            lean4export_tmp_dir.rename(lean4export_dir)
        except Exception as e:
            print(f"  Error moving lean4export directory to final location: {e}")
            return None
    
    return lean4export_dir


def load_yaml_files(directory: Path, schema_name: str) -> list[dict]:
    """Load all YAML files from a directory with schema validation."""
    items = []
    if not directory.exists():
        return items
    for file in directory.glob("*.yaml"):
        with open(file, "r") as f:
            data = yaml.safe_load(f)
            
            # Validate against schema before processing
            validate_yaml_data(data, schema_name, file)
            
            data["_file"] = file.name
            # Derive name from filename (without .yaml extension)
            data["name"] = file.stem
            items.append(data)
    return items


def load_tests() -> list[dict]:
    """Load all test definitions."""
    return load_yaml_files(get_project_root() / "tests", "test")


def expand_tests() -> list[dict]:
    """Load test definitions and expand multiple tests into individual test entries."""
    base_tests = load_tests()
    expanded_tests = []
    
    build_tests_dir = get_project_root() / "_build" / "tests"
    
    for test in base_tests:
        if test.get("multiple", False):
            # This is a multiple test - check if it has been built
            test_dir = build_tests_dir / test["name"]
            if test_dir.exists():
                # Enumerate subtests from good/ and bad/ directories
                good_dir = test_dir / "good"
                bad_dir = test_dir / "bad"
                
                # Process good subtests (expected outcome: accept)
                if good_dir.exists():
                    for ndjson_file in good_dir.glob("*.ndjson"):
                        subtest_name = ndjson_file.stem
                        expanded_test = test.copy()
                        expanded_test["name"] = f"{test['name']}/{subtest_name}"
                        expanded_test["outcome"] = "accept"
                        expanded_test["_is_subtest"] = True
                        expanded_test["_parent_test"] = test["name"]
                        expanded_test["_subtest_name"] = subtest_name
                        expanded_test["_subtest_category"] = "good"
                        expanded_tests.append(expanded_test)
                
                # Process bad subtests (expected outcome: reject)
                if bad_dir.exists():
                    for ndjson_file in bad_dir.glob("*.ndjson"):
                        subtest_name = ndjson_file.stem
                        expanded_test = test.copy()
                        expanded_test["name"] = f"{test['name']}/{subtest_name}"
                        expanded_test["outcome"] = "reject"
                        expanded_test["_is_subtest"] = True
                        expanded_test["_parent_test"] = test["name"]
                        expanded_test["_subtest_name"] = subtest_name
                        expanded_test["_subtest_category"] = "bad"
                        expanded_tests.append(expanded_test)
            # If multiple test directory doesn't exist, skip it (not built yet)
        else:
            # Regular single test
            expanded_tests.append(test)
    
    return expanded_tests


def load_checkers() -> list[dict]:
    """Load all checker definitions."""
    return load_yaml_files(get_project_root() / "checkers", "checker")


def find_test_by_name(name: str) -> dict | None:
    """Find a test by name (including expanded subtests)."""
    for test in expand_tests():
        if test["name"] == name:
            return test
    return None


def find_checker_by_name(name: str) -> dict | None:
    """Find a checker by name."""
    for checker in load_checkers():
        if checker["name"] == name:
            return checker
    return None


# =============================================================================
# Source setup - shared by tests and checkers
# =============================================================================


def setup_source_directory(
    config: dict, 
    base_dir: Path, 
    local_base_path: Path | None = None,
) -> Path | None:
    """Set up a source directory for tests or checkers.
    
    Handles four cases:
    - url: Clone a git repository
    - dir: Use a local directory
    - leanfile: Set up a standalone Test module from a Lean file
    - neither: Create an empty directory
    
    Args:
        config: Test or checker configuration dict with name, url, dir, ref, rev, leanfile
        base_dir: Base directory where the work/build directory should be created
        local_base_path: Base path for local directories (defaults to project root)
    
    Returns the working directory path, or None on failure.
    """
    name = config["name"]
    url = config.get("url")
    local_dir = config.get("dir")
    lean_file_path = config.get("leanfile")
    ref = config.get("ref")
    rev = config.get("rev")

    if local_base_path is None:
        local_base_path = get_project_root()

    work_dir = base_dir / name
    
    # Clean up existing work directory
    if work_dir.exists():
        shutil.rmtree(work_dir)
    work_dir.mkdir(parents=True, exist_ok=True)

    src_dir = work_dir / "src"

    if url:
        # Clone from git repository
        print(f"  Cloning {url}...")
        clone_cmd = ["git", "clone"]
        if ref:
            clone_cmd.extend(["--branch", ref])
        clone_cmd.extend([url, str(src_dir)])

        result = run_cmd(clone_cmd)
        if result.returncode != 0:
            print(f"  Error cloning: {result.stderr}")
            return None

        # Checkout specific revision if specified
        if rev:
            result = run_cmd(["git", "checkout", rev], cwd=src_dir)
            if result.returncode != 0:
                print(f"  Error checking out {rev}: {result.stderr}")
                return None

        return src_dir

    elif local_dir:
        # Use a local directory (copy it to work dir)
        source_dir = local_base_path / local_dir
        if not source_dir.exists():
            print(f"  Source directory not found: {source_dir}")
            return None
        
        shutil.copytree(source_dir, src_dir)
        print(f"  Copied {source_dir} to {src_dir}")
        return src_dir

    elif lean_file_path:
        # Set up a standalone Test module from a Lean file
        source_file = get_project_root() / lean_file_path
        if not source_file.exists():
            print(f"  Source file not found: {source_file}")
            return None
        
        # Create src directory and copy the lean file as Test.lean
        src_dir.mkdir(parents=True, exist_ok=True)
        dest_file = src_dir / "Test.lean"
        shutil.copy(source_file, dest_file)
        print(f"  Copied {source_file} to {dest_file}")
        
        # Copy lean-toolchain from tests/ directory to src directory (for consistency with url flow)
        tests_toolchain = get_project_root() / "tests" / "lean-toolchain"
        dest_toolchain = src_dir / "lean-toolchain"
        if tests_toolchain.exists():
            shutil.copy(tests_toolchain, dest_toolchain)
            print(f"  Copied lean-toolchain from tests/ to src directory")
        else:
            print(f"  Warning: No lean-toolchain file found in tests/ directory")

        # Create a trivial lakefile in the src directory
        lakefile_content = '''name = "test"

[[lean_lib]]
name = "Test"'''
        lakefile_path = src_dir / "lakefile.toml"
        with open(lakefile_path, "w") as f:
            f.write(lakefile_content)
        print(f"  Created trivial lakefile")
        
        return src_dir

    else:
        # Empty directory
        src_dir.mkdir(parents=True, exist_ok=True)
        return src_dir


# =============================================================================
# build-test command
# =============================================================================


def create_test(test: dict, output_dir: Path) -> bool:
    """Create a single test."""
    name = test["name"]
    module = test.get("module")
    run_cmd_str = test.get("run")
    file_path = test.get("file")
    lean_file_path = test.get("leanfile")
    export_decls = test.get("export-decls")
    pre_build = test.get("pre-build")
    multiple = test.get("multiple", False)

    # Determine test type based on fields present
    if module:
        test_type = "module"
    elif run_cmd_str:
        test_type = "run"
    elif lean_file_path:
        test_type = "leanfile"
    elif file_path:
        test_type = "file"
    else:
        print(f"  Error: Test {name} must have 'module', 'run', 'leanfile', or 'file' field")
        return False

    # Validate multiple flag
    if multiple and test_type != "run":
        print(f"  Error: Test {name} uses 'multiple' flag but this is only valid with 'run' field")
        return False

    print(f"Creating test: {name} (type: {test_type}{'multiple' if multiple else ''})")
    output_dir.mkdir(parents=True, exist_ok=True)

    if multiple:
        # For multiple tests, output directory is testname/ instead of testname.ndjson
        final_output_dir = output_dir / name
        tmp_output_dir = output_dir / f"{name}.tmp"
    else:
        # Regular single test
        output_file = output_dir / f"{name}.ndjson"
        tmp_file = output_dir / f"{name}.ndjson.tmp"

    # Handle static file case (no work directory needed)
    if file_path:
        if multiple:
            print(f"  Error: Test {name} cannot use 'multiple' flag with static file")
            return False
        source_file = get_project_root() / file_path
        if not source_file.exists():
            print(f"  Source file not found: {source_file}")
            return False
        shutil.copy(source_file, tmp_file)
        tmp_file.rename(output_file)
        print(f"  Copied {source_file} to {output_file}")
        return True

    # These test types require lean4export
    lean4export_dir = None
    if module or lean_file_path:
        # First set up the work directory to get access to toolchain information
        work_dir = setup_source_directory(test, output_dir / "work")
        if work_dir is None:
            return False
        
        # Get the toolchain from the src directory (consistent for both leanfile and module tests)
        toolchain = get_lean_toolchain(work_dir)
        
        if not toolchain:
            print(f"  Error: No lean-toolchain found in {work_dir}")
            return False
        
        # Set up lean4export for this specific toolchain
        lean4export_dir = setup_lean4export(toolchain)
        if lean4export_dir is None:
            return False
    else:
        # Set up work directory (url, dir, or empty) for non-lean4export tests
        work_dir = setup_source_directory(test, output_dir / "work")
        if work_dir is None:
            return False

    # Run pre-build command if specified
    if pre_build:
        print(f"  Running pre-build: {pre_build}")
        result = run_cmd(pre_build, cwd=work_dir, shell=True)
        if result.returncode != 0:
            print(f"  Pre-build failed: {result.stderr}")
            return False

    # Execute based on test type
    if module or lean_file_path:
        # Both module and leanfile variants use lean4export workflow
        # leanfile is treated like module with hardcoded module name "Test"
        build_dir = work_dir
        
        # Determine module name
        if lean_file_path:
            module_name = "Test"
        else:
            module_name = module
        
        # Build the module
        print(f"  Building module {module_name}...")
        result = run_cmd(f"lake build {module_name}", cwd=build_dir, shell=True)
        if result.returncode != 0:
            print(f"  Build failed: {result.stderr}")
            return False

        # Export using lean4export
        if export_decls and not isinstance(export_decls, list):
            print(f"  Error: export-decls must be a list of strings")
            return False
        
        if export_decls:
            decls_str = ", ".join(export_decls)
            print(f"  Exporting module {module_name} ({decls_str})...")
        else:
            print(f"  Exporting module {module_name} ...")
        
        if not run_lean4export(lean4export_dir, module_name, export_decls, cwd=build_dir, out_file=tmp_file):
            return False

    elif run_cmd_str:
        # Run the script with $OUT environment variable
        print(f"  Running: {run_cmd_str}")
        env = os.environ.copy()
        
        if multiple:
            # For multiple tests, $OUT points to a temporary directory
            tmp_output_dir.mkdir(parents=True, exist_ok=True)
            env["OUT"] = str(tmp_output_dir)
        else:
            # For single tests, $OUT points to the output file
            env["OUT"] = str(tmp_file)

        result = run_cmd(run_cmd_str, cwd=work_dir, shell=True, env=env)
        if result.returncode != 0:
            print(f"  Script failed: {result.stderr}")
            return False

    if multiple:
        # For multiple tests, validate directory structure and move to final location
        if not tmp_output_dir.exists():
            print(f"  Error: Script did not create output directory {tmp_output_dir}")
            return False
            
        # Check that we have good/ and/or bad/ subdirectories with .ndjson files
        good_dir = tmp_output_dir / "good"
        bad_dir = tmp_output_dir / "bad"
        
        subtests_found = []
        if good_dir.exists():
            for ndjson_file in good_dir.glob("*.ndjson"):
                subtest_name = ndjson_file.stem
                subtests_found.append((subtest_name, "good"))
        
        if bad_dir.exists():
            for ndjson_file in bad_dir.glob("*.ndjson"):
                subtest_name = ndjson_file.stem
                subtests_found.append((subtest_name, "bad"))
        
        if not subtests_found:
            print(f"  Error: No .ndjson files found in {tmp_output_dir}/good/ or {tmp_output_dir}/bad/")
            return False
        
        # Move to final location
        if final_output_dir.exists():
            shutil.rmtree(final_output_dir)
        tmp_output_dir.rename(final_output_dir)
        
        # Generate stats for each subtest
        for subtest_name, outcome in subtests_found:
            subtest_file = final_output_dir / outcome / f"{subtest_name}.ndjson"
            
            # Gather stats about the subtest file
            file_size = subtest_file.stat().st_size
            with open(subtest_file, "r") as f:
                line_count = sum(1 for _ in f)
            
            # Format file size and line count
            size_str = format_memory(file_size)
            
            if line_count >= 1_000_000_000:
                lines_str = f"{line_count / 1_000_000_000:.1f}G"
            elif line_count >= 1_000_000:
                lines_str = f"{line_count / 1_000_000:.1f}M"
            elif line_count >= 1_000:
                lines_str = f"{line_count / 1_000:.1f}k"
            else:
                lines_str = str(line_count)
                
            # Write stats JSON file
            stats_file = final_output_dir / outcome / f"{subtest_name}.stats.json"
            stats = {
                "name": f"{name}/{subtest_name}",
                "parent_test": name,
                "subtest_name": subtest_name,
                "outcome": "accept" if outcome == "good" else "reject",
                "size": file_size,
                "size_str": size_str,
                "lines": line_count,
                "lines_str": lines_str,
                "yaml_file": f"tests/{name}.yaml",
            }
            with open(stats_file, "w") as f:
                json.dump(stats, f, indent=2)
        
        print(f"  Created {len(subtests_found)} subtests in {final_output_dir}")
        return True
    
    else:
        # Single test: move tmp file to final location and gather stats
        tmp_file.rename(output_file)

        # Gather stats about the created file
        file_size = output_file.stat().st_size
        with open(output_file, "r") as f:
            line_count = sum(1 for _ in f)
        
        # Format file size in human-readable format
        if file_size >= 1024 * 1024 * 1024:
            size_str = f"{file_size / (1024 * 1024 * 1024):.1f} GB"
        elif file_size >= 1024 * 1024:
            size_str = f"{file_size / (1024 * 1024):.1f} MB"
        elif file_size >= 1024:
            size_str = f"{file_size / 1024:.1f} KB"
        else:
            size_str = f"{file_size} B"

        # Format line count with SI prefixes
        if line_count >= 1_000_000_000:
            lines_str = f"{line_count / 1_000_000_000:.1f}G"
        elif line_count >= 1_000_000:
            lines_str = f"{line_count / 1_000_000:.1f}M"
        elif line_count >= 1_000:
            lines_str = f"{line_count / 1_000:.1f}k"
        else:
            lines_str = str(line_count)

        print(f"  Created {output_file} ({size_str}, {lines_str} lines)")

        # Write stats JSON file
        stats_file = output_dir / f"{name}.stats.json"
        stats = {
            "name": name,
            "size": file_size,
            "size_str": size_str,
            "lines": line_count,
            "lines_str": lines_str,
            "yaml_file": f"tests/{name}.yaml",
        }
        with open(stats_file, "w") as f:
            json.dump(stats, f, indent=2)

        return True


def cmd_build_test(args: argparse.Namespace) -> int:
    """Handle the build-test command."""
    output_dir = get_project_root() / "_build" / "tests"

    if args.name:
        test = find_test_by_name(args.name)
        if test is None:
            print(f"Test not found: {args.name}")
            return 1
        tests = [test]
    else:
        tests = load_tests()

    # Filter out large tests if --no-large flag is set
    if args.no_large:
        original_count = len(tests)
        tests = [test for test in tests if not test.get("large", False)]
        skipped_count = original_count - len(tests)
        if skipped_count > 0:
            print(f"Skipping {skipped_count} large test(s) due to --no-large flag")

    if not tests:
        print("No tests found.")
        return 0

    success = 0
    failed = 0
    for test in tests:
        if create_test(test, output_dir):
            success += 1
        else:
            failed += 1

    print(f"\nResults: {success} succeeded, {failed} failed")
    return 0 if failed == 0 else 1


# =============================================================================
# build-checker command
# =============================================================================


def build_checker(checker: dict, build_dir: Path) -> bool:
    """Build a single checker."""
    name = checker["name"]
    version = checker.get("version", "unknown")
    build_cmd = checker.get("build")

    print(f"Building checker: {name} (version: {version})")

    # Set up source directory (for checkers, local dirs are relative to checkers/ subfolder)
    local_base_path = get_project_root() / "checkers" if checker.get("dir") else get_project_root()
    work_dir = setup_source_directory(checker, build_dir, local_base_path)
    if work_dir is None:
        return False

    # Determine the actual working directory for build commands
    if checker.get("url") or checker.get("dir"):
        # Git repos and local dirs are copied to src/ subdirectory
        actual_work_dir = work_dir
    else:
        # Empty directory case - use the checker directory directly
        actual_work_dir = build_dir / name

    # Run build command if specified
    if build_cmd:
        # Format the build command for display
        if '\n' in build_cmd:
            # Multi-line command: indent each line
            lines = build_cmd.strip().split('\n')
            formatted_cmd = '\n    '.join(lines)
            print(f"  Building:\n    {formatted_cmd}")
        else:
            # Single-line command
            print(f"  Building: {build_cmd}")
        
        result = run_cmd(build_cmd, cwd=actual_work_dir, shell=True)
        if result.returncode != 0:
            print(f"  Build failed: {result.stderr}")
            return False

    print(f"  Checker {name} built successfully")
    return True


def cmd_build_checker(args: argparse.Namespace) -> int:
    """Handle the build-checker command."""
    build_dir = get_project_root() / "_build" / "checkers"

    if args.name:
        checker = find_checker_by_name(args.name)
        if checker is None:
            print(f"Checker not found: {args.name}")
            return 1
        checkers = [checker]
    else:
        checkers = load_checkers()

    if not checkers:
        print("No checkers found.")
        return 0

    success = 0
    failed = 0
    for checker in checkers:
        if build_checker(checker, build_dir):
            success += 1
        else:
            failed += 1

    print(f"\nResults: {success} succeeded, {failed} failed")
    return 0 if failed == 0 else 1


# =============================================================================
# run-checker command
# =============================================================================


def run_checker_on_test(checker: dict, test: dict, build_dir: Path, tests_dir: Path, results_dir: Path) -> dict:
    """Run a checker on a test and return the result."""
    checker_name = checker["name"]
    test_name = test["name"]
    checker_run_cmd = checker["run"]

    # Handle subtest vs regular test file paths
    if test.get("_is_subtest"):
        parent_test = test["_parent_test"]
        subtest_name = test["_subtest_name"]
        category = test["_subtest_category"]
        test_file = tests_dir / parent_test / category / f"{subtest_name}.ndjson"
    else:
        test_file = tests_dir / f"{test_name}.ndjson"
        
    if not test_file.exists():
        result_data = {
            "checker": checker_name,
            "test": test_name,
            "status": "error",
            "message": f"Test file not found: {test_file}",
            "exit_code": -1,
            "wall_time": 0,
            "cpu_time": 0,
            "max_rss": 0,
            "stdout": "",
            "stderr": "",
        }
        # Write result to JSON file (replace "/" with "_" for valid filename)
        results_dir.mkdir(parents=True, exist_ok=True)
        safe_test_name = test_name.replace("/", "_")
        result_file = results_dir / f"{checker_name}_{safe_test_name}.json"
        with open(result_file, "w") as f:
            json.dump(result_data, f, indent=2)
        return result_data

    # Determine working directory
    checker_dir = build_dir / checker_name
    if checker.get("url") or checker.get("dir"):
        work_dir = checker_dir / "src"
    else:
        work_dir = checker_dir

    work_dir.mkdir(parents=True, exist_ok=True)

    # Run the checker and track detailed performance metrics
    # Set up environment with IN variable pointing to test file
    env = os.environ.copy()
    env["IN"] = str(test_file)
    
    result = run_cmd(checker_run_cmd, cwd=work_dir, shell=True, env=env, measure_perf=True)

    exit_code = result.returncode
    if exit_code == 0:
        status = "accepted"
    elif exit_code == 1:
        status = "rejected"
    elif exit_code == 2:
        status = "declined"
    else:
        status = "error"

    result_data = {
        "checker": checker_name,
        "test": test_name,
        "status": status,
        "exit_code": exit_code,
        "wall_time": result.wall_time,
        "cpu_time": result.cpu_time,
        "max_rss": result.max_rss,
        "stdout": result.stdout,
        "stderr": result.stderr,
    }

    # Write result to JSON file (replace "/" with "_" for valid filename)
    results_dir.mkdir(parents=True, exist_ok=True)
    safe_test_name = test_name.replace("/", "_")
    result_file = results_dir / f"{checker_name}_{safe_test_name}.json"
    with open(result_file, "w") as f:
        json.dump(result_data, f, indent=2)

    return result_data


def cmd_run_checker(args: argparse.Namespace) -> int:
    """Handle the run-checker command."""
    build_dir = get_project_root() / "_build" / "checkers"
    tests_dir = get_project_root() / "_build" / "tests"
    results_dir = get_project_root() / "_results"

    # Determine which checkers to run
    if args.checker:
        checker = find_checker_by_name(args.checker)
        if checker is None:
            print(f"Checker not found: {args.checker}")
            return 1
        checkers = [checker]
    else:
        checkers = load_checkers()
        # Filter out checkers that weren't built (no build directory exists)
        built_checkers = []
        skipped_checker_names = []
        for checker in checkers:
            checker_dir = build_dir / checker["name"]
            if checker_dir.exists():
                built_checkers.append(checker)
            else:
                skipped_checker_names.append(checker["name"])
        checkers = built_checkers
        if skipped_checker_names:
            print(f"Skipping {len(skipped_checker_names)} checker(s) that weren't built: {', '.join(skipped_checker_names)}")

    # Determine which tests to run
    if args.test:
        test = find_test_by_name(args.test)
        if test is None:
            print(f"Test not found: {args.test}")
            return 1
        tests = [test]
    else:
        tests = expand_tests()
        # Filter out tests that weren't built (no .ndjson file exists)
        built_tests = []
        skipped_test_names = []
        for test in tests:
            if test.get("_is_subtest"):
                # For subtests, check the specific subtest file
                parent_test = test["_parent_test"]
                subtest_name = test["_subtest_name"]
                category = test["_subtest_category"]
                test_file = tests_dir / parent_test / category / f"{subtest_name}.ndjson"
            else:
                # For regular tests, check the regular file
                test_file = tests_dir / f"{test['name']}.ndjson"
            
            if test_file.exists():
                built_tests.append(test)
            else:
                skipped_test_names.append(test["name"])
        tests = built_tests
        if skipped_test_names:
            print(f"Skipping {len(skipped_test_names)} test(s) that weren't built: {', '.join(skipped_test_names)}")

    if not checkers:
        print("No built checkers found.")
        return 0

    if not tests:
        print("No built tests found.")
        return 0

    # Sort tests by line count for consistent processing order
    test_stats = load_test_stats()
    tests = sort_tests_by_line_count(tests, test_stats)

    results = []
    for checker in checkers:
        for test in tests:
            print(f"Running {checker['name']} on {test['name']}...", end="\n" if VERBOSE else " ", flush=True)
            result = run_checker_on_test(checker, test, build_dir, tests_dir, results_dir)
            results.append(result)
            print(f"[{result['status']}, {format_duration(result['wall_time'])}]", flush=True)

    # Summary
    print("\n" + "=" * 60)
    print("Summary:")
    print("=" * 60)

    status_counts = {"accepted": 0, "rejected": 0, "declined": 0, "error": 0}
    for r in results:
        status_counts[r["status"]] = status_counts.get(r["status"], 0) + 1

    for status, count in status_counts.items():
        if count > 0:
            print(f"  {status}: {count}")

    return 0


# =============================================================================
# build-site command
# =============================================================================


def load_results() -> dict:
    """Load all result JSON files from _results directory.
    
    Returns a dict keyed by (checker_name, test_name) tuples.
    """
    results = {}
    results_dir = get_project_root() / "_results"
    if not results_dir.exists():
        return results
    
    for file in results_dir.glob("*.json"):
        with open(file, "r") as f:
            data = json.load(f)
            key = (data["checker"], data["test"])
            results[key] = data
    
    return results


def load_test_stats() -> dict:
    """Load all test stats JSON files from _build/tests directory.
    
    Returns a dict keyed by test name (including subtests like "parent/subtest").
    """
    stats = {}
    stats_dir = get_project_root() / "_build" / "tests"
    if not stats_dir.exists():
        return stats
    
    # Load regular test stats
    for file in stats_dir.glob("*.stats.json"):
        with open(file, "r") as f:
            data = json.load(f)
            stats[data["name"]] = data
    
    # Load multiple test stats (from subdirectories)
    for test_dir in stats_dir.iterdir():
        if test_dir.is_dir():
            # Check for good/ and bad/ subdirectories
            for category in ["good", "bad"]:
                category_dir = test_dir / category
                if category_dir.exists():
                    for stats_file in category_dir.glob("*.stats.json"):
                        with open(stats_file, "r") as f:
                            data = json.load(f)
                            stats[data["name"]] = data
    
    return stats


def sort_tests_by_line_count(tests: list[dict], test_stats: dict) -> list[dict]:
    """Sort tests by line count in ascending order.
    
    Args:
        tests: List of test dictionaries
        test_stats: Dictionary of test stats keyed by test name
        
    Returns:
        Sorted list of tests (ascending by line count)
    """
    def get_line_count(test):
        test_name = test["name"]
        if test_name in test_stats:
            return test_stats[test_name].get("lines", 0)
        return 0
    
    return sorted(tests, key=get_line_count)


def compute_checker_stats(checker: dict, tests: list[dict], results: dict) -> dict:
    """Compute statistics for a checker across all tests.
    
    Returns a dict with:
    - accept_correct: number of tests with outcome=accept that checker accepted
    - accept_total: number of tests with outcome=accept that weren't declined
    - reject_correct: number of tests with outcome=reject that checker rejected
    - reject_total: number of tests with outcome=reject that weren't declined
    - declined_count: number of tests that checker declined
    - mathlib_time: wall time for the mathlib test (or None)
    - mathlib_cpu_time: CPU time for the mathlib test (or None)
    - mathlib_max_rss: Max RSS for the mathlib test (or None)
    """
    checker_name = checker["name"]
    
    accept_correct = 0
    accept_total = 0
    reject_correct = 0
    reject_total = 0
    declined_count = 0
    mathlib_time = None
    mathlib_cpu_time = None
    mathlib_max_rss = None
    
    for test in tests:
        test_name = test["name"]
        expected_outcome = test.get("outcome")
        
        key = (checker_name, test_name)
        result = results.get(key)
        
        if result is None:
            continue
        
        status = result.get("status")
        
        # Track mathlib performance metrics only if the test was accepted
        if test_name == "mathlib" and status == "accepted":
            mathlib_time = result.get("wall_time")
            mathlib_cpu_time = result.get("cpu_time")
            mathlib_max_rss = result.get("max_rss")
        
        # Count declined tests
        if status == "declined":
            declined_count += 1
            continue
        
        if expected_outcome == "accept":
            accept_total += 1
            if status == "accepted":
                accept_correct += 1
        elif expected_outcome == "reject":
            reject_total += 1
            if status == "rejected":
                reject_correct += 1
    
    return {
        "accept_correct": accept_correct,
        "accept_total": accept_total,
        "reject_correct": reject_correct,
        "reject_total": reject_total,
        "declined_count": declined_count,
        "mathlib_time": mathlib_time,
        "mathlib_cpu_time": mathlib_cpu_time,
        "mathlib_max_rss": mathlib_max_rss,
    }


def get_build_metadata() -> dict:
    """Get build metadata including timestamp, git revision, and GitHub action info."""
    metadata = {
        "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S UTC"),
        "git_revision": None,
        "git_revision_short": None,
        "github_url": None,
        "github_action_url": None,
    }
    
    # Get git revision
    try:
        result = run_cmd(["git", "rev-parse", "HEAD"], capture_output=True)
        if result.returncode == 0:
            git_revision = result.stdout.strip()
            metadata["git_revision"] = git_revision
            metadata["git_revision_short"] = git_revision[:8]
            # Build GitHub URL (assuming GitHub)
            try:
                remote_result = run_cmd(["git", "remote", "get-url", "origin"], capture_output=True)
                if remote_result.returncode == 0:
                    remote_url = remote_result.stdout.strip()
                    # Convert git URL to GitHub web URL
                    if "github.com" in remote_url:
                        if remote_url.startswith("git@"):
                            # Convert git@github.com:user/repo.git to https://github.com/user/repo
                            repo_path = remote_url.split(":")[-1].replace(".git", "")
                            metadata["github_url"] = f"https://github.com/{repo_path}/commit/{git_revision}"
                        elif remote_url.startswith("https://"):
                            repo_path = remote_url.replace("https://github.com/", "").replace(".git", "")
                            metadata["github_url"] = f"https://github.com/{repo_path}/commit/{git_revision}"
            except:
                pass
    except:
        pass
    
    # Get GitHub Action info from environment variables
    github_server = os.environ.get("GITHUB_SERVER_URL")
    github_repo = os.environ.get("GITHUB_REPOSITORY")
    github_run_id = os.environ.get("GITHUB_RUN_ID")
    
    if github_server and github_repo and github_run_id:
        metadata["github_run_id"] = github_run_id
        metadata["github_action_url"] = f"{github_server}/{github_repo}/actions/runs/{github_run_id}"
    
    return metadata


def generate_source_links(config: dict, config_type: str, git_revision: str | None = None) -> dict:
    """Generate Declaration and Source links for a test or checker configuration.
    
    Args:
        config: Test or checker configuration dict
        config_type: "tests" or "checkers" 
        git_revision: Git revision for GitHub links
        
    Returns dict with:
        declaration_url: Link to the YAML file in GitHub
        source_url: Link to the source (either URL or local dir in GitHub)
    """
    links = {
        "declaration_url": None,
        "source_url": None,
    }
    
    if not git_revision:
        return links
    
    # Generate declaration URL (YAML file in GitHub)
    base_github_url = "https://github.com/leanprover/lean-kernel-arena"
    declaration_path = f"{config_type}/{config['name']}.yaml"
    links["declaration_url"] = f"{base_github_url}/blob/{git_revision}/{declaration_path}"
    
    # Generate source URL
    url = config.get("url")
    local_dir = config.get("dir")
    leanfile = config.get("leanfile")
    rev = config.get("rev")
    
    if url:
        # External repository - check if it's a GitHub URL and we have a rev
        if rev and "github.com" in url:
            # Convert repository URL to tree/commit URL
            if url.endswith(".git"):
                repo_url = url[:-4]  # Remove .git suffix
            else:
                repo_url = url
            links["source_url"] = f"{repo_url}/tree/{rev}"
        else:
            # Use the repository URL as-is
            links["source_url"] = url
    elif local_dir:
        # Local directory in this repository
        if config_type == "checkers":
            source_path = f"checkers/{local_dir}"
        else:
            source_path = local_dir
        links["source_url"] = f"{base_github_url}/tree/{git_revision}/{source_path}"
    elif leanfile:
        # Lean file in this repository
        links["source_url"] = f"{base_github_url}/blob/{git_revision}/{leanfile}"
    
    return links


def create_test_tarball(tests: list, output_dir: Path) -> dict:
    """Create a tarball containing test files, organized by expected outcome.
    
    Returns dict with tarball_size (in bytes), good_count, and bad_count.
    """
    import tarfile
    import os
    
    tarball_path = output_dir / "lean-arena-tests.tar.gz"
    build_tests_dir = get_project_root() / "_build" / "tests"
    
    good_count = 0
    bad_count = 0
    
    with tarfile.open(tarball_path, "w:gz") as tar:
        for test in tests:
            # Skip large tests
            if test.get("large", False):
                continue
            
            if test.get("_is_subtest"):
                # Handle subtests
                parent_test = test["_parent_test"]
                subtest_name = test["_subtest_name"]
                category = test["_subtest_category"]
                test_file = build_tests_dir / parent_test / category / f"{subtest_name}.ndjson"
                
                if test_file.exists():
                    outcome = test.get("outcome", "unknown")
                    if outcome == "accept":
                        subdir = "good"
                        good_count += 1
                    else:
                        subdir = "bad"
                        bad_count += 1
                    
                    # Use the full test name (parent/subtest) for the archive name
                    arcname = f"{subdir}/{test['name']}.ndjson"
                    tar.add(test_file, arcname=arcname)
            else:
                # Handle regular tests
                test_file = build_tests_dir / f"{test['name']}.ndjson"
                if not test_file.exists():
                    continue
                    
                outcome = test.get("outcome", "unknown")
                if outcome == "accept":
                    subdir = "good"
                    good_count += 1
                else:
                    subdir = "bad"
                    bad_count += 1
                
                # Add file to tarball with appropriate subdirectory
                arcname = f"{subdir}/{test['name']}.ndjson"
                tar.add(test_file, arcname=arcname)
    
    # Get tarball size
    tarball_size = tarball_path.stat().st_size if tarball_path.exists() else 0
    
    return {
        "tarball_size": tarball_size,
        "good_count": good_count,
        "bad_count": bad_count
    }


def cmd_build_site(args: argparse.Namespace) -> int:
    """Handle the build-site command."""
    output_dir = Path(args.outdir)
    output_dir.mkdir(parents=True, exist_ok=True)

    templates_dir = get_project_root() / "templates"
    if not templates_dir.exists():
        print(f"Templates directory not found: {templates_dir}")
        return 1

    env = Environment(
        loader=FileSystemLoader(templates_dir),
        autoescape=select_autoescape(),
    )

    tests = expand_tests()
    checkers = load_checkers()
    results = load_results()
    test_stats = load_test_stats()
    
    # Compute stats for each checker
    for checker in checkers:
        checker["stats"] = compute_checker_stats(checker, tests, results)

    # Sort checkers by the specified criteria:
    # 1. Number of bad tests not rejected (ascending - fewer mistakes is better)
    # 2. Number of good tests accepted (descending - more is good)  
    # 3. Number of good tests not accepted (ascending - fewer mistakes is better) 
    # 4. Number of tests declined (ascending - fewer declines is better)
    # 5. Wall time for processing mathlib (ascending, with None values last)
    def sort_key(checker):
        stats = checker["stats"]
        bad_not_rejected = stats["reject_total"] - stats["reject_correct"]  # Should be low
        good_accepted = stats["accept_correct"]  # Should be high
        good_not_accepted = stats["accept_total"] - stats["accept_correct"]  # Should be low
        declined_count = stats["declined_count"]  # Should be low
        mathlib_time = stats["mathlib_time"]
        
        # For mathlib_time: None values should be treated as infinity (sort last)
        time_sort_key = mathlib_time if mathlib_time is not None else float('inf')
        
        # Note: For descending sort on good_accepted, we negate it
        return (bad_not_rejected, -good_accepted, good_not_accepted, declined_count, time_sort_key)
    
    checkers.sort(key=sort_key)

    # Get build metadata
    build_info = get_build_metadata()

    # Create test tarball
    tarball_info = create_test_tarball(tests, output_dir)

    # Build context data
    data = {
        "tests": tests,
        "checkers": checkers,
        "format_duration": format_duration,
        "format_memory": format_memory,
        "build_info": build_info,
        "tarball_info": tarball_info,
    }

    # Render index.html
    try:
        template = env.get_template("index.html")
        output_file = output_dir / "index.html"
        template.stream(data).dump(str(output_file))
        print(f"Generated: {output_file}")
    except Exception as e:
        print(f"Error rendering template: {e}")
        return 1

    # Generate per-checker pages
    try:
        checker_template = env.get_template("checker.html")
        for checker in checkers:
            checker_dir = output_dir / "checker" / checker["name"]
            checker_dir.mkdir(parents=True, exist_ok=True)
            
            # Generate checker links
            checker_links = generate_source_links(checker, "checkers", build_info.get("git_revision"))
            
            # Gather results for this checker
            checker_results = []
            for test in tests:
                key = (checker["name"], test["name"])
                if key in results:
                    result = results[key].copy()
                    result["expected"] = test.get("outcome")
                    # Add test stats
                    if test["name"] in test_stats:
                        result["test_stats"] = test_stats[test["name"]]
                    # Add test links
                    result["test_links"] = generate_source_links(test, "tests", build_info.get("git_revision"))
                    # Add test description (rendered from markdown)
                    result["test_description"] = render_markdown(test.get("description", ""))
                    checker_results.append(result)
            
            # Sort checker results by line count (ascending order)
            def get_result_line_count(result):
                test_stats_data = result.get("test_stats", {})
                return test_stats_data.get("lines", 0)
            
            checker_results.sort(key=get_result_line_count)
            
            # Create a copy of checker data with rendered description
            checker_with_rendered_desc = checker.copy()
            checker_with_rendered_desc["description"] = render_markdown(checker.get("description", ""))
            
            checker_data = {
                "checker": checker_with_rendered_desc,
                "checker_links": checker_links,
                "results": checker_results,
                "format_duration": format_duration,
                "format_memory": format_memory,
                "build_info": build_info,
            }
            
            output_file = checker_dir / "index.html"
            checker_template.stream(checker_data).dump(str(output_file))
            print(f"Generated: {output_file}")
    except Exception as e:
        print(f"Error rendering checker template: {e}")
        return 1

    # Copy static files if they exist
    static_dir = templates_dir / "static"
    if static_dir.exists():
        shutil.copytree(static_dir, output_dir / "static", dirs_exist_ok=True)
        print(f"Copied static files to: {output_dir / 'static'}")

    print(f"\nSite built successfully in: {output_dir}")
    return 0


# =============================================================================
# Main entry point
# =============================================================================


def main() -> int:
    """Main entry point."""
    global VERBOSE
    
    parser = argparse.ArgumentParser(
        prog="lka",
        description="Lean Kernel Arena - Tool for managing Lean kernel tests and checkers",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Print commands being executed and their stats",
    )
    subparsers = parser.add_subparsers(dest="command", help="Available commands")

    # build-test command
    build_test_parser = subparsers.add_parser(
        "build-test",
        help="Build test files from test definitions",
    )
    build_test_parser.add_argument(
        "name",
        nargs="?",
        help="Name of the test to build (default: all tests)",
    )
    build_test_parser.add_argument(
        "--no-large",
        action="store_true",
        help="Skip large tests (marked with 'large: true' in YAML)",
    )

    # build-checker command
    build_checker_parser = subparsers.add_parser(
        "build-checker",
        help="Build checkers from checker definitions",
    )
    build_checker_parser.add_argument(
        "name",
        nargs="?",
        help="Name of the checker to build (default: all checkers)",
    )

    # run-checker command
    run_checker_parser = subparsers.add_parser(
        "run-checker",
        help="Run checkers on tests",
    )
    run_checker_parser.add_argument(
        "--checker",
        help="Name of the checker to run (default: all checkers)",
    )
    run_checker_parser.add_argument(
        "--test",
        help="Name of the test to run (default: all tests)",
    )

    # build-site command
    build_site_parser = subparsers.add_parser(
        "build-site",
        help="Build the website",
    )
    build_site_parser.add_argument(
        "--outdir",
        default="_out",
        help="Output directory for the website (default: _out)",
    )

    args = parser.parse_args()
    
    # Set global verbose flag
    VERBOSE = args.verbose

    if args.command is None:
        parser.print_help()
        return 0

    if args.command == "build-test":
        return cmd_build_test(args)
    elif args.command == "build-checker":
        return cmd_build_checker(args)
    elif args.command == "run-checker":
        return cmd_run_checker(args)
    elif args.command == "build-site":
        return cmd_build_site(args)
    else:
        parser.print_help()
        return 1


if __name__ == "__main__":
    sys.exit(main())
