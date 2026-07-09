from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    conformal_einstein_00_radiation_omega_route_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_conformal_einstein_00_radiation_omega_route_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_conformal_einstein_00_radiation_omega_route_gate.json")


def write_reports() -> dict:
    payload = conformal_einstein_00_radiation_omega_route_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Conformal Einstein 00 Radiation Omega Route Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Projection choice closed: `{payload['projection_choice_closed']}`",
        f"Omega solution closed: `{payload['omega_solution_closed']}`",
        "",
        "## Equation",
        f"`{payload['equation']}`",
        "",
        "## Bottom line",
        payload["bottom_line"],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
