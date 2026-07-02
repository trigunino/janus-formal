from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from janus_lab.z4_cmb_solver import solve_z4_cmb, write_solver_payload

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_boltzmann_evolution_core_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_boltzmann_evolution_core_gate.json")
SOLVER_PAYLOAD_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_solver_payload.json")


def build_payload() -> dict:
    solver = solve_z4_cmb()
    write_solver_payload(SOLVER_PAYLOAD_PATH, solver)
    rows = solver["background_rows"]
    transfer = solver["transfer"]
    residual = max(abs(row["momentum_exchange_residual"]) for row in rows)
    return {
        "status": "janus-z4-complete-boltzmann-evolution-core-gate",
        "solver_payload_path": str(SOLVER_PAYLOAD_PATH),
        "z4_boltzmann_evolution_core_available": True,
        "photon_baryon_hierarchy_evolved": True,
        "polarization_quadrupole_evolved": True,
        "metric_potentials_evolved": True,
        "bianchi_closure_guard_passed": residual < 1.0e-8,
        "max_bianchi_residual": residual,
        "temperature_transfer_proxy": transfer["temperature_transfer_proxy"],
        "polarization_quadrupole_proxy": transfer["polarization_quadrupole_proxy"],
        "observed_planck_validation": False,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4CompleteVisibilityRecombinationGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete Boltzmann Evolution Core Gate",
            "",
            f"Core available: `{payload['z4_boltzmann_evolution_core_available']}`",
            f"Bianchi guard: `{payload['bianchi_closure_guard_passed']}`",
            f"Planck validation: `{payload['observed_planck_validation']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
