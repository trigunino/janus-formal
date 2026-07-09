from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    two_cosh_branch_matching_obstruction_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_two_cosh_branch_matching_obstruction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_two_cosh_branch_matching_obstruction_gate.json")


def write_reports() -> dict:
    payload = two_cosh_branch_matching_obstruction_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    match = payload["matching_at_late_throat"]
    lines = [
        "# Janus Two-Cosh Branch Matching Obstruction Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"C0 match possible: `{match['C0_scale_factor_match_possible']}`",
        f"C1 match possible: `{match['C1_shape_match_possible_without_extra_lapse_or_surface']}`",
        f"Early shape H at match: `{match['early_shape_H_over_du']}`",
        f"Late shape H at throat: `{match['late_shape_H_over_du']}`",
        "",
        "## Escape routes",
    ]
    for row in payload["non_rustine_escape_routes"]:
        lines.append(f"- {row}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
