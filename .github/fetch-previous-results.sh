#!/usr/bin/env bash
# Downloads the results of the latest build of master into the directory given
# as the first argument, for `lka.py ci-select` to reuse what is still valid.
#
# These are the "all-results" artifact of the newest run of this workflow on
# master that has one (a run that was cancelled, for example, has none). Only
# runs of master itself count: a pull request from a fork may well come from a
# branch named master, too. If there is no such run (artifacts expire), the
# directory stays empty and everything is run anew. That is also what happens
# if the runs cannot be listed, which is no reason to fail the build.
#
# Needs GH_TOKEN (with actions: read) and GH_REPO.
set -euo pipefail

dir="$1"
mkdir -p "$dir"

if ! runs=$(gh run list --workflow build-and-deploy.yml --branch master --limit 50 \
  --json databaseId,event \
  --jq '.[] | select(.event == "push" or .event == "workflow_dispatch") | .databaseId'); then
  echo "::warning::Could not list the builds of master; running everything anew"
  exit 0
fi

for run in $runs; do
  # Most runs simply have no such artifact (any more); the error message
  # stays in the log in case it is something else
  if gh run download "$run" --name all-results --dir "$dir"; then
    echo "Fetched the results of run $run" >&2
    exit 0
  fi
  # Do not keep anything a failed download may have left behind
  rm -rf "$dir"
  mkdir -p "$dir"
done

echo "Found no earlier results of master to reuse" >&2
