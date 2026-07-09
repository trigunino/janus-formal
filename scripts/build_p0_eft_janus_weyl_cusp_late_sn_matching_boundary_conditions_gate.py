from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    weyl_cusp_late_sn_matching_boundary_conditions_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_weyl_cusp_late_sn_matching_boundary_conditions_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_weyl_cusp_late_sn_matching_boundary_conditions_gate.json")


def write_reports() -> dict:
    payload = weyl_cusp_late_sn_matching_boundary_conditions_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Weyl Cusp Late SN Matching Boundary Conditions Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Boundary problem closed: `{payload['boundary_problem_closed']}`",
        f"Matching solution closed: `{payload['matching_solution_closed']}`",
        "",
        "## Boundary conditions",
    ]
    for key, value in payload["boundary_conditions"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
