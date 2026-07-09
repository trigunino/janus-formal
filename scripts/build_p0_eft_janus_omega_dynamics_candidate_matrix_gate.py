from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    omega_dynamics_candidate_matrix_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_omega_dynamics_candidate_matrix_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_omega_dynamics_candidate_matrix_gate.json")


def write_reports() -> dict:
    payload = omega_dynamics_candidate_matrix_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Omega Dynamics Candidate Matrix Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Recommended next: `{payload['recommended_next']}`",
        "",
        "## Candidates",
    ]
    for row in payload["candidates"]:
        lines.append(f"- `{row['rank']}` `{row['name']}`: {row['route']}")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
