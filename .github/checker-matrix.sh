#!/usr/bin/env bash
# Selects the checkers to run in CI and prints them as a "checkers=<JSON
# array>" line, suitable for appending to $GITHUB_OUTPUT.
#
# Normally all enabled checkers are selected. On pull requests that touch
# nothing but checker configurations, only the touched checkers are selected.
set -euo pipefail

all=$(uv run lka.py list-checkers --json)
selected="$all"

if [ "${GITHUB_EVENT_NAME:-}" = "pull_request" ]; then
  # Diff the PR head commit against its merge base with the target branch.
  # BASE_SHA and HEAD_SHA are set from the event payload in the workflow;
  # computing the merge base requires a full-history checkout.
  changed=$(git diff --name-only "$BASE_SHA...$HEAD_SHA")
  if [ -n "$changed" ] && ! grep -qv '^checkers/[^/]*\.yaml$' <<< "$changed"; then
    touched=$(sed -e 's!^checkers/!!' -e 's!\.yaml$!!' <<< "$changed" | jq --raw-input . | jq --slurp --compact-output .)
    # Restrict to the touched checkers, as far as they (still) exist and are
    # enabled. If none are left (e.g. the PR deletes a checker), fall back to
    # running all of them.
    selected=$(jq --compact-output --argjson touched "$touched" 'map(select(. as $c | $touched | index($c)))' <<< "$all")
    if [ "$selected" = "[]" ]; then
      selected="$all"
    fi
  fi
fi

echo "Selected checkers: $selected" >&2
echo "checkers=$selected"
