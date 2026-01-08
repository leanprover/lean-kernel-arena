#!/usr/bin/env python3
"""Lean Kernel Arena - Tool for managing Lean kernel tests and checkers."""

import argparse
import datetime
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import yaml
from jinja2 import Environment, FileSystemLoader, select_autoescape

# Global verbose flag
VERBOSE = False


def get_project_root() -> Path:
    """Get the project root directory."""
    return Path(__file__).parent.resolve()


def format_duration(seconds: float) -> str:
    """Format a duration in seconds to a human-readable string."""
    if seconds >= 3600:
        return f"{seconds / 3600:.1f}h"
    elif seconds >= 60:
        return f"{seconds / 60:.1f}m"
    elif seconds >= 1:
        return f"{seconds:.1f}s"
    else:
        return f"{seconds * 1000:.0f}ms"


def run_cmd(
    cmd: str | list[str],
    cwd: Path | None = None,
    env: dict | None = None,
    shell: bool = False,
    capture_output: bool = True,
) -> subprocess.CompletedProcess:
    """Run a command with optional verbose output.
    
    Args:
        cmd: Command to run (string for shell=True, list for shell=False)
        cwd: Working directory
        env: Environment variables
        shell: Whether to run as shell command
        capture_output: Whether to capture stdout/stderr
    
    Returns:
        CompletedProcess instance
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
    
    if VERBOSE:
        status = "ok" if result.returncode == 0 else f"FAILED (exit {result.returncode})"
        print(f"      -> {status} in {format_duration(elapsed)}")
    
    return result


def load_yaml_files(directory: Path) -> list[dict]:
    """Load all YAML files from a directory."""
    items = []
    if not directory.exists():
        return items
    for file in directory.glob("*.yaml"):
        with open(file, "r") as f:
            data = yaml.safe_load(f)
            data["_file"] = file.name
            # Derive name from filename (without .yaml extension)
            data["name"] = file.stem
            items.append(data)
    return items


def load_tests() -> list[dict]:
    """Load all test definitions."""
    return load_yaml_files(get_project_root() / "tests")


def load_checkers() -> list[dict]:
    """Load all checker definitions."""
    return load_yaml_files(get_project_root() / "checkers")


def find_test_by_name(name: str) -> dict | None:
    """Find a test by name."""
    for test in load_tests():
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
# create-test command
# =============================================================================


def setup_work_dir(test: dict, output_dir: Path) -> Path | None:
    """Set up the working directory for a test.
    
    Handles three cases:
    - url: Clone a git repository
    - dir: Use a local directory
    - neither: Create an empty directory
    
    Returns the working directory path, or None on failure.
    """
    name = test["name"]
    url = test.get("url")
    local_dir = test.get("dir")
    ref = test.get("ref")
    rev = test.get("rev")

    work_dir = output_dir / "work" / name
    
    # Clean up existing work directory
    if work_dir.exists():
        shutil.rmtree(work_dir)
    work_dir.mkdir(parents=True, exist_ok=True)

    if url:
        # Clone from git repository
        print(f"  Cloning {url}...")
        clone_cmd = ["git", "clone"]
        if ref:
            clone_cmd.extend(["--branch", ref])
        clone_cmd.extend([url, str(work_dir / "repo")])

        result = run_cmd(clone_cmd)
        if result.returncode != 0:
            print(f"  Error cloning: {result.stderr}")
            return None

        repo_dir = work_dir / "repo"

        # Checkout specific revision if specified
        if rev:
            result = run_cmd(["git", "checkout", rev], cwd=repo_dir)
            if result.returncode != 0:
                print(f"  Error checking out {rev}: {result.stderr}")
                return None

        return repo_dir

    elif local_dir:
        # Use a local directory (copy it to work dir)
        source_dir = get_project_root() / local_dir
        if not source_dir.exists():
            print(f"  Source directory not found: {source_dir}")
            return None
        
        repo_dir = work_dir / "repo"
        shutil.copytree(source_dir, repo_dir)
        print(f"  Copied {source_dir} to {repo_dir}")
        return repo_dir

    else:
        # Empty directory
        repo_dir = work_dir / "repo"
        repo_dir.mkdir(parents=True, exist_ok=True)
        return repo_dir


def create_test(test: dict, output_dir: Path) -> bool:
    """Create a single test."""
    name = test["name"]
    module = test.get("module")
    run_cmd_str = test.get("run")
    file_path = test.get("file")
    pre_build = test.get("pre-build")

    # Determine test type based on fields present
    if module:
        test_type = "module"
    elif run_cmd_str:
        test_type = "run"
    elif file_path:
        test_type = "file"
    else:
        print(f"  Error: Test {name} must have 'module', 'run', or 'file' field")
        return False

    print(f"Creating test: {name} (type: {test_type})")
    output_dir.mkdir(parents=True, exist_ok=True)
    output_file = output_dir / f"{name}.ndjson"
    tmp_file = output_dir / f"{name}.ndjson.tmp"

    # Handle static file case (no work directory needed)
    if file_path:
        source_file = get_project_root() / file_path
        if not source_file.exists():
            print(f"  Source file not found: {source_file}")
            return False
        shutil.copy(source_file, tmp_file)
        tmp_file.rename(output_file)
        print(f"  Copied {source_file} to {output_file}")
        return True

    # Set up work directory (url, dir, or empty)
    work_dir = setup_work_dir(test, output_dir)
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
    if module:
        # Set up lean4export in a sibling directory
        # TODO: Check out a tag based on the lean-toolchain of the test repository
        lean4export_dir = work_dir.parent / "lean4export"
        if not lean4export_dir.exists():
            print(f"  Cloning lean4export...")
            clone_cmd = ["git", "clone", "--branch", "json_output",
                        "https://github.com/ammkrn/lean4export",
                        str(lean4export_dir)]
            result = run_cmd(clone_cmd)
            if result.returncode != 0:
                print(f"  Error cloning lean4export: {result.stderr}")
                return False

            print(f"  Building lean4export...")
            result = run_cmd("lake build", cwd=lean4export_dir, shell=True)
            if result.returncode != 0:
                print(f"  Error building lean4export: {result.stderr}")
                return False

        # Build the module in the repo
        print(f"  Building module {module}...")
        result = run_cmd(f"lake build {module}", cwd=work_dir, shell=True)
        if result.returncode != 0:
            print(f"  Build failed: {result.stderr}")
            return False

        # Export using lean4export
        print(f"  Exporting module {module}...")
        lean4export_bin = lean4export_dir / ".lake" / "build" / "bin" / "lean4export"
        export_cmd = f"lake env {lean4export_bin} {module} > {tmp_file}"

        result = run_cmd(export_cmd, cwd=work_dir, shell=True)
        if result.returncode != 0:
            print(f"  Export failed: {result.stderr}")
            return False

    elif run_cmd_str:
        # Run the script with $OUT environment variable
        print(f"  Running: {run_cmd_str}")
        env = os.environ.copy()
        env["OUT"] = str(tmp_file)

        result = run_cmd(run_cmd_str, cwd=work_dir, shell=True, env=env)
        if result.returncode != 0:
            print(f"  Script failed: {result.stderr}")
            return False

    # Move tmp file to final location upon success
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


def cmd_create_test(args: argparse.Namespace) -> int:
    """Handle the create-test command."""
    output_dir = get_project_root() / "_build" / "tests"

    if args.name:
        test = find_test_by_name(args.name)
        if test is None:
            print(f"Test not found: {args.name}")
            return 1
        tests = [test]
    else:
        tests = load_tests()

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
    url = checker.get("url")
    local_dir = checker.get("dir")
    ref = checker.get("ref")
    rev = checker.get("rev")
    build_cmd = checker.get("build")

    print(f"Building checker: {name} (version: {version})")

    checker_dir = build_dir / name
    checker_dir.mkdir(parents=True, exist_ok=True)

    # Clone repository if URL is provided
    if url:
        repo_dir = checker_dir / "repo"
        if repo_dir.exists():
            shutil.rmtree(repo_dir)

        print(f"  Cloning {url}...")
        clone_cmd = ["git", "clone", "--depth=1"]
        if ref:
            clone_cmd.extend(["--branch", ref])
        clone_cmd.extend([url, str(repo_dir)])

        result = run_cmd(clone_cmd)
        if result.returncode != 0:
            print(f"  Error cloning: {result.stderr}")
            return False

        # Checkout specific revision if specified
        if rev:
            result = run_cmd(["git", "checkout", rev], cwd=repo_dir)
            if result.returncode != 0:
                print(f"  Error checking out {rev}: {result.stderr}")
                return False

        work_dir = repo_dir
    elif local_dir:
        # Use a local directory (copy it to work dir)
        source_dir = get_project_root() / "checkers" / local_dir
        if not source_dir.exists():
            print(f"  Source directory not found: {source_dir}")
            return False
        
        repo_dir = checker_dir / "repo"
        if repo_dir.exists():
            shutil.rmtree(repo_dir)
        shutil.copytree(source_dir, repo_dir)
        print(f"  Copied {source_dir} to {repo_dir}")
        work_dir = repo_dir
    else:
        work_dir = checker_dir

    # Run build command if specified
    if build_cmd:
        print(f"  Building: {build_cmd}")
        result = run_cmd(build_cmd, cwd=work_dir, shell=True)
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

    test_file = tests_dir / f"{test_name}.ndjson"
    if not test_file.exists():
        result_data = {
            "checker": checker_name,
            "test": test_name,
            "status": "error",
            "message": f"Test file not found: {test_file}",
            "exit_code": -1,
            "duration": 0,
            "stdout": "",
            "stderr": "",
        }
        # Write result to JSON file
        results_dir.mkdir(parents=True, exist_ok=True)
        result_file = results_dir / f"{checker_name}_{test_name}.json"
        with open(result_file, "w") as f:
            json.dump(result_data, f, indent=2)
        return result_data

    # Determine working directory
    checker_dir = build_dir / checker_name
    if checker.get("url") or checker.get("dir"):
        work_dir = checker_dir / "repo"
    else:
        work_dir = checker_dir

    work_dir.mkdir(parents=True, exist_ok=True)

    # Run the checker and track time
    # Set up environment with IN variable pointing to test file
    env = os.environ.copy()
    env["IN"] = str(test_file)
    
    start_time = time.time()
    result = run_cmd(checker_run_cmd, cwd=work_dir, shell=True, env=env)
    duration = time.time() - start_time

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
        "duration": duration,
        "stdout": result.stdout,
        "stderr": result.stderr,
    }

    # Write result to JSON file
    results_dir.mkdir(parents=True, exist_ok=True)
    result_file = results_dir / f"{checker_name}_{test_name}.json"
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

    # Determine which tests to run
    if args.test:
        test = find_test_by_name(args.test)
        if test is None:
            print(f"Test not found: {args.test}")
            return 1
        tests = [test]
    else:
        tests = load_tests()

    if not checkers:
        print("No checkers found.")
        return 0

    if not tests:
        print("No tests found.")
        return 0

    results = []
    for checker in checkers:
        for test in tests:
            print(f"Running {checker['name']} on {test['name']}...", end="\n" if VERBOSE else " ", flush=True)
            result = run_checker_on_test(checker, test, build_dir, tests_dir, results_dir)
            results.append(result)
            print(f"[{result['status']}]")

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
    
    Returns a dict keyed by test name.
    """
    stats = {}
    stats_dir = get_project_root() / "_build" / "tests"
    if not stats_dir.exists():
        return stats
    
    for file in stats_dir.glob("*.stats.json"):
        with open(file, "r") as f:
            data = json.load(f)
            stats[data["name"]] = data
    
    return stats


def compute_checker_stats(checker: dict, tests: list[dict], results: dict) -> dict:
    """Compute statistics for a checker across all tests.
    
    Returns a dict with:
    - accept_correct: number of tests with outcome=accept that checker accepted
    - accept_total: number of tests with outcome=accept that weren't declined
    - reject_correct: number of tests with outcome=reject that checker rejected
    - reject_total: number of tests with outcome=reject that weren't declined
    - declined_count: number of tests that checker declined
    - mathlib_time: duration for the mathlib test (or None)
    """
    checker_name = checker["name"]
    
    accept_correct = 0
    accept_total = 0
    reject_correct = 0
    reject_total = 0
    declined_count = 0
    mathlib_time = None
    
    for test in tests:
        test_name = test["name"]
        expected_outcome = test.get("outcome")
        
        key = (checker_name, test_name)
        result = results.get(key)
        
        if result is None:
            continue
        
        status = result.get("status")
        
        # Track mathlib time
        if test_name == "mathlib" and result.get("duration") is not None:
            mathlib_time = result["duration"]
        
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
        metadata["github_action_url"] = f"{github_server}/{github_repo}/actions/runs/{github_run_id}"
    
    return metadata


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

    tests = load_tests()
    checkers = load_checkers()
    results = load_results()
    test_stats = load_test_stats()
    
    # Compute stats for each checker
    for checker in checkers:
        checker["stats"] = compute_checker_stats(checker, tests, results)

    # Get build metadata
    build_info = get_build_metadata()

    # Build context data
    data = {
        "tests": tests,
        "checkers": checkers,
        "format_duration": format_duration,
        "build_info": build_info,
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
            
            # Read the raw YAML file for display
            checker_yaml_path = get_project_root() / "checkers" / f"{checker['name']}.yaml"
            checker_yaml = ""
            if checker_yaml_path.exists():
                with open(checker_yaml_path, "r") as f:
                    checker_yaml = f.read()
            
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
                    # Add test YAML content
                    test_yaml_path = get_project_root() / "tests" / f"{test['name']}.yaml"
                    if test_yaml_path.exists():
                        with open(test_yaml_path, "r") as f:
                            result["test_yaml"] = f.read()
                    checker_results.append(result)
            
            checker_data = {
                "checker": checker,
                "checker_yaml": checker_yaml,
                "results": checker_results,
                "format_duration": format_duration,
                "build_info": build_info,
            }
            
            output_file = checker_dir / "index.html"
            checker_template.stream(checker_data).dump(str(output_file))
            print(f"Generated: {output_file}")
    except Exception as e:
        print(f"Error rendering checker template: {e}")
        return 1
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

    # create-test command
    create_test_parser = subparsers.add_parser(
        "create-test",
        help="Create test files from test definitions",
    )
    create_test_parser.add_argument(
        "name",
        nargs="?",
        help="Name of the test to create (default: all tests)",
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

    if args.command == "create-test":
        return cmd_create_test(args)
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
