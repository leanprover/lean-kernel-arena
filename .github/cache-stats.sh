#!/usr/bin/env bash
# Report how full the Namespace cache volume is in the job log, and warn when
# it is getting full. Usage: cache-stats.sh <label>
set -uo pipefail

echo "Cache volume ($1):"
df -h /cache
du -sh ~/.cache/lean-kernel-arena ~/.cache/mathlib ~/.elan 2>/dev/null

used=$(df --output=pcent /cache | tail -1 | tr -dc 0-9)
if [ "$used" -ge 80 ]; then
  echo "::warning::Cache volume is ${used}% full, consider increasing nscloud-cache-size"
fi
