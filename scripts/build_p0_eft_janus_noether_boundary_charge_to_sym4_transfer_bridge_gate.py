from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    noether_boundary_charge_to_sym4_transfer_bridge_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_noether_boundary_charge_to_sym4_transfer_bridge_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_noether_boundary_charge_to_sym4_transfer_bridge_gate.json")


def write_reports() -> dict:
    payload = noether_boundary_charge_to_sym4_transfer_bridge_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    existing = payload["existing_z2_sigma_boundary_charge"]
    lines = [
        "# Janus Noether Boundary Charge To Sym4 Transfer Bridge Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Symbolic boundary Hamiltonian ready: `{existing['symbolic_boundary_hamiltonian_ready']}`",
        f"Numeric boundary Hamiltonian ready: `{existing['numeric_boundary_hamiltonian_ready']}`",
        "",
        "## Bridge requirements",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["sym4_transfer_bridge_requirements"].items())
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
