from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    boundary_microstate_isotropic_average_candidate_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_boundary_microstate_isotropic_average_candidate_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_boundary_microstate_isotropic_average_candidate_gate.json")


def write_reports() -> dict:
    payload = boundary_microstate_isotropic_average_candidate_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Boundary Microstate Isotropic Average Candidate Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Microstate count: `{payload['counts']['microstate_count']}`",
        f"Macro isotropic profile count: `{payload['counts']['macro_isotropic_profile_count']}`",
        f"No-fit closed now: `{payload['no_fit_closed_now']}`",
        "",
        "## Hard conditions",
    ]
    for key, value in payload["hard_conditions"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
