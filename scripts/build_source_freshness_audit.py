from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/source_freshness_audit.md")
JSON_PATH = Path("outputs/reports/source_freshness_audit.json")


def build_payload() -> dict:
    entries = [
        {
            "ref_id": "X2026-questionable-black-holes",
            "title": "Questionable Black Holes",
            "url": "http://www.jp-petit.org/papers/cosmo/2026-01-12-Journal-of-Modern-Physics-QUESTIONABLE-BLACK-HOLES.pdf",
            "local_status": "downloaded-indexed",
            "axis": "compact_objects",
            "impact": "no change to cosmological lensing/S8 route",
        },
        {
            "ref_id": "X2026-complex-reality",
            "title": "The Real World as a part of a Complex Reality",
            "url": "http://www.jp-petit.org/papers/cosmo/2026-The-Real-World-as-a-part-of-a-Complex-Reality.pdf",
            "local_status": "downloaded-indexed",
            "axis": "math_symmetry",
            "impact": "symmetry roadmap only; no direct tensor-lensing closure",
        },
    ]
    return {
        "description": "Freshness audit after checking jp-petit.org/papers/cosmo on 2026-06-21.",
        "checked_index": "https://www.jp-petit.org/papers/cosmo/",
        "local_library_size": 42,
        "new_entries": entries,
        "main_route": [
            "Keep M15/M30 as field-equation/geodesic anchors.",
            "Keep M18 and X2026-expansion-desi for expansion geometry.",
            "Keep X2026-variable-constants for early-gauge/ruler hypotheses.",
            "Do not replace the Bianchi closure target with compact-object or symmetry-roadmap papers.",
        ],
        "verdict": (
            "Latest source check is integrated. No newly found source removes the current "
            "Bianchi/Q_det/Q_cross blockers for survey-level Janus lensing."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Source Freshness Audit",
        "",
        payload["description"],
        "",
        f"Checked index: `{payload['checked_index']}`.",
        f"Local library size: {payload['local_library_size']} PDFs.",
        "",
        "| ref | title | axis | local status | impact |",
        "|---|---|---|---|---|",
    ]
    for row in payload["new_entries"]:
        lines.append(
            f"| {row['ref_id']} | {row['title']} | {row['axis']} | "
            f"{row['local_status']} | {row['impact']} |"
        )
    lines.extend(["", "## Main Route", ""])
    lines.extend(f"- {item}" for item in payload["main_route"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
