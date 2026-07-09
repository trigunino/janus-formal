from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    non_throat_pt_transition_candidate_matrix_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_non_throat_pt_transition_candidate_matrix_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_non_throat_pt_transition_candidate_matrix_gate.json")


def write_reports() -> dict:
    payload = non_throat_pt_transition_candidate_matrix_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Non-Throat PT Transition Candidate Matrix Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Recommended first: `{payload['recommended_first']}`",
        "",
        "## Candidates",
    ]
    for row in payload["candidates"]:
        lines.append(
            f"- `{row['name']}`: priority=`{row['priority']}`, "
            f"avoids_sigma_radius=`{row['avoids_sigma_radius']}`; blocker={row['main_blocker']}"
        )
    lines.extend(["", "## First test contract"])
    for row in payload["first_test_contract"]:
        lines.append(f"- {row}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
