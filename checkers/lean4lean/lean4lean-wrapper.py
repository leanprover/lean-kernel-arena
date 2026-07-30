#!/usr/bin/env python3
"""
Wrapper for lean4lean that manages multiple versions based on Lean toolchains.
"""
import sys
import os
import json
import subprocess
from pathlib import Path

# Map from Lean toolchains to lean4lean git tags
TOOLCHAIN_TO_TAG = {
    "4.29.0": ("arena/v4.29.0","50005444cce5317cc6cc044c9f0f36b54682b59f"),
    "4.29.1": ("arena/v4.29.0","50005444cce5317cc6cc044c9f0f36b54682b59f"),
}

# Base directory for lean4lean builds
BUILD_DIR = Path(__file__).parent

def run_cmd(cmd, cwd=None, check=True):
    """Run a command and return the result."""
    print(f"Running: {' '.join(cmd)}", file=sys.stderr)
    result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if check and result.returncode != 0:
        print(f"Command failed with exit code {result.returncode}", file=sys.stderr)
        print(f"stdout: {result.stdout}", file=sys.stderr)
        print(f"stderr: {result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result

def build_lean4lean(tag_sha):
    """Clone and build a specific version of lean4lean."""
    tag, sha = tag_sha
    build_path = BUILD_DIR / sha
    
    if build_path.exists():
        print(f"lean4lean {tag} ({sha}) already built at {build_path}", file=sys.stderr)
        return build_path
    
    print(f"Building lean4lean {tag} ({sha})...", file=sys.stderr)
    BUILD_DIR.mkdir(parents=True, exist_ok=True)
    
    # Clone the repository
    run_cmd([
        "git", "clone",
        "https://github.com/nomeata/lean4lean.git",
        str(build_path)
    ])
    
    # Checkout the specific SHA
    run_cmd(["git", "checkout", sha], cwd=build_path)
    
    # Build with lake
    run_cmd(["lake", "build", "lean4lean"], cwd=build_path)
    
    print(f"Successfully built lean4lean {tag} ({sha})", file=sys.stderr)
    return build_path

def cmd_build():
    """Build all lean4lean versions."""
    print("Building all lean4lean versions...", file=sys.stderr)
    # Get unique tags to avoid building the same version multiple times
    unique_tags = set(TOOLCHAIN_TO_TAG.values())
    for tag in unique_tags:
        build_lean4lean(tag)
    print("All versions built successfully", file=sys.stderr)
    return 0

def cmd_run(ndjson_file):
    """Run lean4lean on the given NDJSON file."""
    if not os.path.exists(ndjson_file):
        print(f"Error: File not found: {ndjson_file}", file=sys.stderr)
        return 2
    
    # Read the first line to get metadata
    with open(ndjson_file, 'r') as f:
        first_line = f.readline().strip()
    
    if not first_line:
        print("Error: Empty file", file=sys.stderr)
        return 2
    
    try:
        metadata = json.loads(first_line)
    except json.JSONDecodeError as e:
        print(f"Error: Failed to parse metadata from first line: {e}", file=sys.stderr)
        return 2
    
    # Extract the toolchain
    toolchain = metadata.get("meta", {}).get("lean", {}).get("version")
    if not toolchain:
        print("Error: No toolchain found in metadata", file=sys.stderr)
        return 2
    
    # Look up the corresponding tag and sha
    tag_sha = TOOLCHAIN_TO_TAG.get(toolchain)
    if not tag_sha:
        print(f"Error: Unknown toolchain: {toolchain}", file=sys.stderr)
        print(f"Known toolchains: {', '.join(TOOLCHAIN_TO_TAG.keys())}", file=sys.stderr)
        return 2
    
    tag, sha = tag_sha
    
    # Check if the build exists
    build_path = BUILD_DIR / sha
    if not build_path.exists():
        print(f"Error: lean4lean {tag} ({sha}) not built. Run 'build' command first.", file=sys.stderr)
        return 2
    
    # Run lean4lean
    lean4lean_bin = build_path / ".lake" / "build" / "bin" / "lean4lean"
    if not lean4lean_bin.exists():
        print(f"Error: lean4lean binary not found at {lean4lean_bin}", file=sys.stderr)
        return 2
    
    # Execute lean4lean with the NDJSON file
    result = subprocess.run([str(lean4lean_bin), "--import", ndjson_file], check=False)
    return result.returncode

def main():
    if len(sys.argv) < 2:
        print("Usage: lean4lean-wrapper.py <build|run> [args...]", file=sys.stderr)
        return 1
    
    command = sys.argv[1]
    
    if command == "build":
        return cmd_build()
    elif command == "run":
        if len(sys.argv) < 3:
            print("Usage: lean4lean-wrapper.py run <file.ndjson>", file=sys.stderr)
            return 1
        return cmd_run(sys.argv[2])
    else:
        print(f"Unknown command: {command}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    sys.exit(main())
