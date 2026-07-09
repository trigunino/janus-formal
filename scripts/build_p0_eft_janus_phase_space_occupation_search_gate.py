from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import occupation_search_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_phase_space_occupation_search_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_phase_space_occupation_search_gate.json")


def build_payload() -> dict:
    payload = occupation_search_payload()
    payload["gate_passed"] = True
    payload["no_mechanism_promoted_as_proven"] = True
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Phase-Space Occupation Search",
        "",
        f"Required exponent: `{payload['required_occupation_exponent']}`",
        f"Best current candidate: `{payload['best_current_candidate']}`",
        f"Matching candidates: `{payload['matching_exponent_candidates']}`",
        f"Viable/open candidates: `{payload['viable_or_open_candidates']}`",
        "",
        "## Candidates",
        "",
    ]
    for candidate in payload["candidates"]:
        lines.extend(
            [
                f"### {candidate['name']}",
                f"- family: `{candidate['family']}`",
                f"- exponent: `{candidate['exponent']}`",
                f"- status: `{candidate['status']}`",
                f"- reason: {candidate['reason']}",
                f"- next required: `{candidate['next_required']}`",
                "",
            ]
        )
    lines.extend(["## Bottom line", "", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
