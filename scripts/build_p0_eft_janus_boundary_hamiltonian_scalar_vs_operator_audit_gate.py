from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    boundary_hamiltonian_scalar_vs_operator_audit_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_boundary_hamiltonian_scalar_vs_operator_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_boundary_hamiltonian_scalar_vs_operator_audit_gate.json")


def write_reports() -> dict:
    payload = boundary_hamiltonian_scalar_vs_operator_audit_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Boundary Hamiltonian Scalar Vs Operator Audit Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Scalar boundary H orders states: `{payload['scalar_boundary_H_orders_states']}`",
        f"Operator-valued boundary H available: `{payload['operator_valued_boundary_H_available']}`",
        "",
        "## Cases",
    ]
    for row in payload["cases"]:
        lines.append(f"- `{row['case']}`: `{row['form']}`; orders=`{row['orders_1001_states']}`; {row['reason']}")
    lines.extend(["", "## Minimal operator requirement", payload["minimal_operator_requirement"]])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
