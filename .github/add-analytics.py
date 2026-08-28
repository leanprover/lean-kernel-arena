#!/usr/bin/env python3
"""Insert the analytics snippet into the pages that are about to be deployed.

This is deliberately not part of the templates. A round is archived as a
tarball, deposited on Zenodo and cited by DOI, and whoever opens that copy in
ten years should not have their browser call out to a third party. So the
built site stays clean, and the snippet is added to the deployed pages only,
as the last thing before they are handed to GitHub Pages.

Usage: add-analytics.py <snippet.html> <directory>
"""

import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.exit(__doc__)
    snippet = Path(argv[1]).read_text()
    root = Path(argv[2])
    if not root.is_dir():
        sys.exit(f"Not a directory: {root}")

    inserted, skipped = 0, []
    for html in sorted(root.rglob("*.html")):
        text = html.read_text(errors="surrogateescape")
        if "</head>" not in text:
            # Not a full page; nothing to do, but say so rather than silently
            # leaving a deployed page untracked.
            skipped.append(html.relative_to(root))
            continue
        html.write_text(text.replace("</head>", snippet + "</head>", 1),
                        errors="surrogateescape")
        inserted += 1

    print(f"Inserted {argv[1]} into {inserted} HTML files below {root}")
    for path in skipped:
        print(f"  no </head>, left alone: {path}")
    if not inserted:
        sys.exit(f"No HTML files with a </head> found below {root}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
