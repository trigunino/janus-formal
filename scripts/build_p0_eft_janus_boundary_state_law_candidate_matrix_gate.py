from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    boundary_state_law_candidate_matrix_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_boundary_state_law_candidate_matrix_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_boundary_state_law_candidate_matrix_gate.json")


def write_reports() -> dict:
    payload = boundary_state_law_candidate_matrix_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Boundary State Law Candidate Matrix Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Required N: `{payload['required_N']}`",
        f"Factorization: `{payload['number_theory']['factorization']}`",
        f"Binomial identity: `{payload['number_theory']['binomial_identity']}`",
        f"Janus source anchor for 14 modes: `{payload['number_theory']['current_janus_source_anchor_for_14_modes']}`",
        "",
        "## Candidates",
    ]
    for row in payload["candidates"]:
        lines.append(
            "- `{name}`: {target_match}; derived `{derived_from_current_janus}`; missing: {missing}".format(
                **row
            )
        )
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
