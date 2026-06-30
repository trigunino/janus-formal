from __future__ import annotations

import argparse
import csv
import re
import sys
from pathlib import Path


TEXT_DIR = Path("data/raw/janus_library_text")
MANIFEST_PATH = Path("data/raw/janus_library/manifest.csv")


def load_titles() -> dict[str, str]:
    if not MANIFEST_PATH.exists():
        return {}
    with MANIFEST_PATH.open(encoding="utf-8") as handle:
        return {row["ref_id"]: row["title"] for row in csv.DictReader(handle)}


def ref_id_from_path(path: Path) -> str:
    return path.name.split("_", 1)[0]


def normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def find_snippets(text: str, pattern: re.Pattern[str], window: int) -> list[str]:
    snippets: list[str] = []
    for match in pattern.finditer(text):
        start = max(0, match.start() - window)
        end = min(len(text), match.end() + window)
        snippets.append(normalize(text[start:end]))
    return snippets


def main() -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    parser = argparse.ArgumentParser(description="Search local Janus PDF text extracts.")
    parser.add_argument("query", help="case-insensitive regex query")
    parser.add_argument("--limit", type=int, default=20, help="maximum snippets to print")
    parser.add_argument("--window", type=int, default=220, help="characters around each match")
    parser.add_argument("--ref", action="append", default=[], help="restrict to a ref id, repeatable")
    args = parser.parse_args()

    titles = load_titles()
    pattern = re.compile(args.query, re.IGNORECASE)
    refs = set(args.ref)
    printed = 0

    for path in sorted(TEXT_DIR.glob("*.txt")):
        ref_id = ref_id_from_path(path)
        if refs and ref_id not in refs:
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        snippets = find_snippets(text, pattern, args.window)
        for snippet in snippets:
            print(f"\n[{ref_id}] {titles.get(ref_id, path.stem)}")
            print(snippet)
            printed += 1
            if printed >= args.limit:
                return


if __name__ == "__main__":
    main()
