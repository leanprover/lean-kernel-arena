#!/usr/bin/env python3
"""Deposit a closed round on Zenodo, to give it a citable DOI.

The DOI has to be known *before* the site is built, because it is shown on the
round's index page. Zenodo supports this: creating a deposition reserves a DOI
that only becomes active on publication. The round build therefore runs

    reserve  -> create a draft deposition, print its pre-reserved DOI
    (build the site with that DOI baked in)
    upload   -> attach the built files to the draft
    publish  -> make the record (and the DOI) public

Publishing is irreversible, so it runs last, once the release exists and all
its assets are uploaded; `discard` deletes the still unpublished draft again
when an earlier step fails.

Rounds after the first are created as new versions of the previous round's
deposition (`--previous-deposition`). That gives them a shared concept DOI
that always resolves to the newest round, next to the per-round DOIs.

Uses only the standard library, so it needs no dependencies beyond the Python
in the dev shell. Authentication is via the ZENODO_TOKEN environment variable.
"""

import argparse
import datetime
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path

# Static deposition metadata (creators, license, ...) lives in the repository
# so that it can be reviewed and changed without touching this script.
METADATA_FILE = Path(__file__).resolve().parent.parent / ".zenodo.json"


def api_base(sandbox: bool) -> str:
    return "https://sandbox.zenodo.org" if sandbox else "https://zenodo.org"


def request(method: str, url: str, token: str, data=None, content_type="application/json"):
    """Perform an API request and return the parsed JSON response (or None)."""
    body = json.dumps(data).encode() if data is not None else None
    req = urllib.request.Request(url, data=body, method=method)
    req.add_header("Authorization", f"Bearer {token}")
    if body is not None:
        req.add_header("Content-Type", content_type)
    try:
        with urllib.request.urlopen(req) as response:
            raw = response.read()
    except urllib.error.HTTPError as e:
        detail = e.read().decode(errors="replace")
        sys.exit(f"Zenodo API error: {method} {url} -> {e.code} {e.reason}\n{detail}")
    if not raw:
        return None
    return json.loads(raw)


def upload_file(bucket_url: str, path: Path, token: str) -> None:
    """Upload one file to a deposition's bucket (streamed, not read into memory)."""
    url = f"{bucket_url}/{path.name}"
    size = path.stat().st_size
    with open(path, "rb") as f:
        req = urllib.request.Request(url, data=f, method="PUT")
        req.add_header("Authorization", f"Bearer {token}")
        req.add_header("Content-Type", "application/octet-stream")
        req.add_header("Content-Length", str(size))
        try:
            with urllib.request.urlopen(req) as response:
                response.read()
        except urllib.error.HTTPError as e:
            detail = e.read().decode(errors="replace")
            sys.exit(f"Zenodo upload failed: {path.name} -> {e.code} {e.reason}\n{detail}")
    print(f"Uploaded {path.name} ({size} bytes)")


def deposition_metadata(round_name: str, url: str) -> dict:
    """Build the deposition metadata for a round from .zenodo.json."""
    with open(METADATA_FILE, "r") as f:
        # Keys starting with an underscore are comments for human readers;
        # Zenodo rejects metadata fields it does not know.
        metadata = {k: v for k, v in json.load(f).items() if not k.startswith("_")}
    metadata["title"] = f"Lean Kernel Arena, Round {round_name}"
    metadata["version"] = round_name
    metadata["publication_date"] = datetime.date.today().isoformat()
    related = list(metadata.get("related_identifiers", []))
    # The same round, served on the web. Point at that rather than at the
    # GitHub release it is distributed from: the release is where the bytes
    # happen to live, the round page is what a reader wants to be sent to.
    related.append({
        "relation": "isIdenticalTo",
        "identifier": url,
        "resource_type": "dataset",
    })
    metadata["related_identifiers"] = related
    return metadata


def prereserved_doi(deposition: dict) -> str:
    doi = deposition.get("metadata", {}).get("prereserve_doi", {}).get("doi")
    if not doi:
        sys.exit(f"Zenodo did not pre-reserve a DOI for deposition {deposition.get('id')}")
    return doi


def emit_outputs(**outputs) -> None:
    """Print outputs, and write them to $GITHUB_OUTPUT when running in Actions."""
    lines = [f"{key}={value}" for key, value in outputs.items()]
    for line in lines:
        print(line)
    github_output = os.environ.get("GITHUB_OUTPUT")
    if github_output:
        with open(github_output, "a") as f:
            f.write("\n".join(lines) + "\n")


def cmd_reserve(args: argparse.Namespace, token: str) -> None:
    base = api_base(args.sandbox)

    if args.previous_deposition:
        # Continue the version chain, so all rounds share a concept DOI
        print(f"Creating a new version of deposition {args.previous_deposition}")
        result = request(
            "POST",
            f"{base}/api/deposit/depositions/{args.previous_deposition}/actions/newversion",
            token,
        )
        draft_url = result.get("links", {}).get("latest_draft")
        if not draft_url:
            sys.exit(f"Zenodo returned no draft for the new version of {args.previous_deposition}")
        deposition = request("GET", draft_url, token)
        # A new version inherits the previous version's files. Drop them: the
        # site tarball is named after its round, so the previous round's copy
        # would otherwise linger in this record next to this round's own.
        for existing in deposition.get("files", []):
            request(
                "DELETE",
                f"{base}/api/deposit/depositions/{deposition['id']}/files/{existing['id']}",
                token,
            )
            print(f"Removed inherited file {existing.get('filename')}")
    else:
        print("Creating a new deposition (first round)")
        deposition = request("POST", f"{base}/api/deposit/depositions", token, data={})

    deposition_id = deposition["id"]
    doi = prereserved_doi(deposition)

    updated = request(
        "PUT",
        f"{base}/api/deposit/depositions/{deposition_id}",
        token,
        data={"metadata": deposition_metadata(args.round, args.url)},
    )

    # Setting metadata must not disturb the reservation: the DOI is about to be
    # baked into the built site, so a changed one has to fail the build.
    if prereserved_doi(updated) != doi:
        sys.exit(
            f"Pre-reserved DOI changed from {doi} to {prereserved_doi(updated)} "
            f"while setting metadata; aborting rather than publishing a wrong DOI"
        )

    bucket = updated.get("links", {}).get("bucket")
    if not bucket:
        sys.exit(f"Deposition {deposition_id} has no file bucket")

    print(f"Draft deposition: {base}/deposit/{deposition_id}")
    emit_outputs(doi=doi, deposition_id=deposition_id, bucket=bucket)


def cmd_upload(args: argparse.Namespace, token: str) -> None:
    for name in args.files:
        path = Path(name)
        if not path.is_file():
            sys.exit(f"Not a file: {path}")
        upload_file(args.bucket, path, token)


def cmd_publish(args: argparse.Namespace, token: str) -> None:
    base = api_base(args.sandbox)
    result = request(
        "POST",
        f"{base}/api/deposit/depositions/{args.deposition}/actions/publish",
        token,
    )
    doi = result.get("doi")
    print(f"Published {result.get('links', {}).get('record_html')} as {doi}")
    emit_outputs(doi=doi, concept_doi=result.get("conceptdoi", ""))


def cmd_discard(args: argparse.Namespace, token: str) -> None:
    """Delete an unpublished draft, so a failed build leaves nothing behind."""
    base = api_base(args.sandbox)
    request("DELETE", f"{base}/api/deposit/depositions/{args.deposition}", token)
    print(f"Discarded draft deposition {args.deposition}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sandbox",
        action="store_true",
        help="Use sandbox.zenodo.org instead of zenodo.org (for test-round-* tags)",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    reserve = subparsers.add_parser("reserve", help="Create a draft deposition and pre-reserve its DOI")
    reserve.add_argument("--round", required=True, help="Round name, e.g. 2026-10")
    reserve.add_argument("--url", required=True, help="Canonical address of the round on the site, e.g. https://arena.lean-lang.org/round/2026-10/")
    reserve.add_argument(
        "--previous-deposition",
        help="Deposition id of the previous round; the new round becomes a new version of it",
    )

    upload = subparsers.add_parser("upload", help="Upload files to a draft deposition")
    upload.add_argument("--bucket", required=True, help="Bucket URL reported by reserve")
    upload.add_argument("files", nargs="+", help="Files to upload")

    publish = subparsers.add_parser("publish", help="Publish a draft deposition (irreversible)")
    publish.add_argument("--deposition", required=True, help="Deposition id reported by reserve")

    discard = subparsers.add_parser("discard", help="Delete an unpublished draft deposition")
    discard.add_argument("--deposition", required=True, help="Deposition id reported by reserve")

    args = parser.parse_args()

    token = os.environ.get("ZENODO_TOKEN")
    if not token:
        sys.exit("ZENODO_TOKEN is not set")

    {
        "reserve": cmd_reserve,
        "upload": cmd_upload,
        "publish": cmd_publish,
        "discard": cmd_discard,
    }[args.command](args, token)
    return 0


if __name__ == "__main__":
    sys.exit(main())
