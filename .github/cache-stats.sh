#!/usr/bin/env bash
# Report how full the Namespace cache volume is, in the job log and the step
# summary, and warn when it is getting full. Usage: cache-stats.sh <label>
set -uo pipefail

{
  echo "### Cache volume ($1)"
  echo '```'
  df -h /cache
  du -sh ~/.cache/lake ~/.cache/mathlib ~/.cache/nix ~/.elan 2>/dev/null
  echo '```'
} | tee -a "$GITHUB_STEP_SUMMARY"

used=$(df --output=pcent /cache | tail -1 | tr -dc 0-9)
if [ "$used" -ge 80 ]; then
  echo "::warning::Cache volume is ${used}% full"
fi
