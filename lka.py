#!/usr/bin/env python3
"""Lean Kernel Arena - Tool for managing Lean kernel tests and checkers."""

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

import yaml
from jinja2 import Environment, FileSystemLoader, select_autoescape


def get_project_root() -> Path:
    """Get the project root directory."""
    return Path(__file__).parent.resolve()


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

        result = subprocess.run(clone_cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"  Error cloning: {result.stderr}")
            return None

        repo_dir = work_dir / "repo"

        # Checkout specific revision if specified
        if rev:
            result = subprocess.run(
                ["git", "checkout", rev],
                cwd=repo_dir,
                capture_output=True,
                text=True,
            )
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
    run_cmd = test.get("run")
    file_path = test.get("file")
    pre_build = test.get("pre-build")

    # Determine test type based on fields present
    if module:
        test_type = "module"
    elif run_cmd:
        test_type = "run"
    elif file_path:
        test_type = "file"
    else:
        print(f"  Error: Test {name} must have 'module', 'run', or 'file' field")
        return False

    print(f"Creating test: {name} (type: {test_type})")
    output_dir.mkdir(parents=True, exist_ok=True)
    output_file = output_dir / f"{name}.ndjson"

    # Handle static file case (no work directory needed)
    if file_path:
        source_file = get_project_root() / file_path
        if not source_file.exists():
            print(f"  Source file not found: {source_file}")
            return False
        shutil.copy(source_file, output_file)
        print(f"  Copied {source_file} to {output_file}")
        return True

    # Set up work directory (url, dir, or empty)
    work_dir = setup_work_dir(test, output_dir)
    if work_dir is None:
        return False

    # Run pre-build command if specified
    if pre_build:
        print(f"  Running pre-build: {pre_build}")
        result = subprocess.run(
            pre_build,
            shell=True,
            cwd=work_dir,
            capture_output=True,
            text=True,
        )
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
            result = subprocess.run(clone_cmd, capture_output=True, text=True)
            if result.returncode != 0:
                print(f"  Error cloning lean4export: {result.stderr}")
                return False

            print(f"  Building lean4export...")
            result = subprocess.run(
                "lake build",
                shell=True,
                cwd=lean4export_dir,
                capture_output=True,
                text=True,
            )
            if result.returncode != 0:
                print(f"  Error building lean4export: {result.stderr}")
                return False

        # Build the module in the repo
        print(f"  Building module {module}...")
        result = subprocess.run(
            f"lake build {module}",
            shell=True,
            cwd=work_dir,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            print(f"  Build failed: {result.stderr}")
            return False

        # Export using lean4export
        print(f"  Exporting module {module}...")
        lean4export_bin = lean4export_dir / ".lake" / "build" / "bin" / "lean4export"
        export_cmd = f"lake env {lean4export_bin} {module} > {output_file}"

        result = subprocess.run(
            export_cmd,
            shell=True,
            cwd=work_dir,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            print(f"  Export failed: {result.stderr}")
            return False

    elif run_cmd:
        # Run the script with $OUT environment variable
        print(f"  Running: {run_cmd}")
        env = os.environ.copy()
        env["OUT"] = str(output_file)

        result = subprocess.run(
            run_cmd,
            shell=True,
            cwd=work_dir,
            capture_output=True,
            text=True,
            env=env,
        )
        if result.returncode != 0:
            print(f"  Script failed: {result.stderr}")
            return False

    print(f"  Created {output_file}")
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

        result = subprocess.run(clone_cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"  Error cloning: {result.stderr}")
            return False

        # Checkout specific revision if specified
        if rev:
            result = subprocess.run(
                ["git", "checkout", rev],
                cwd=repo_dir,
                capture_output=True,
                text=True,
            )
            if result.returncode != 0:
                print(f"  Error checking out {rev}: {result.stderr}")
                return False

        work_dir = repo_dir
    else:
        work_dir = checker_dir

    # Run build command if specified
    if build_cmd:
        print(f"  Building: {build_cmd}")
        result = subprocess.run(
            build_cmd,
            shell=True,
            cwd=work_dir,
            capture_output=True,
            text=True,
        )
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


def run_checker_on_test(checker: dict, test: dict, build_dir: Path, tests_dir: Path) -> dict:
    """Run a checker on a test and return the result."""
    checker_name = checker["name"]
    test_name = test["name"]
    run_cmd = checker["run"]

    test_file = tests_dir / f"{test_name}.ndjson"
    if not test_file.exists():
        return {
            "checker": checker_name,
            "test": test_name,
            "status": "error",
            "message": f"Test file not found: {test_file}",
            "exit_code": -1,
        }

    # Determine working directory
    checker_dir = build_dir / checker_name
    if checker.get("url"):
        work_dir = checker_dir / "repo"
    else:
        work_dir = checker_dir

    work_dir.mkdir(parents=True, exist_ok=True)

    # Run the checker
    full_cmd = f"{run_cmd} {test_file}"
    result = subprocess.run(
        full_cmd,
        shell=True,
        cwd=work_dir,
        capture_output=True,
        text=True,
    )

    exit_code = result.returncode
    if exit_code == 0:
        status = "accepted"
    elif exit_code == 1:
        status = "rejected"
    elif exit_code == 2:
        status = "declined"
    else:
        status = "error"

    return {
        "checker": checker_name,
        "test": test_name,
        "status": status,
        "exit_code": exit_code,
        "stdout": result.stdout,
        "stderr": result.stderr,
    }


def cmd_run_checker(args: argparse.Namespace) -> int:
    """Handle the run-checker command."""
    build_dir = get_project_root() / "_build" / "checkers"
    tests_dir = get_project_root() / "_build" / "tests"

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
            print(f"Running {checker['name']} on {test['name']}...", end=" ")
            result = run_checker_on_test(checker, test, build_dir, tests_dir)
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

    # Build context data
    data = {
        "tests": tests,
        "checkers": checkers,
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
    parser = argparse.ArgumentParser(
        prog="lka",
        description="Lean Kernel Arena - Tool for managing Lean kernel tests and checkers",
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
