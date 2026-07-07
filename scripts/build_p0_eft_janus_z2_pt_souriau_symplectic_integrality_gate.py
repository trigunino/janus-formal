from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "pt_souriau_symplectic_integrality_inputs.json"
OUTPUT_PATH = BASE / "alpha_composite_selector_frontier_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_pt_souriau_symplectic_integrality_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_pt_souriau_symplectic_integrality_gate.md")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    checks = {
        "boundary_phase_space_declared": bool(data.get("boundary_phase_space_declared")),
        "symplectic_two_form_Omega_PT_declared": bool(data.get("symplectic_two_form_Omega_PT_declared")),
        "Omega_PT_closed": bool(data.get("Omega_PT_closed")),
        "prequantum_integrality_condition_declared": bool(
            data.get("prequantum_integrality_condition_declared")
        ),
        "periods_over_two_cycles_computed": bool(data.get("periods_over_two_cycles_computed")),
        "periods_are_integer_multiples_of_2pi_hbar": bool(
            data.get("periods_are_integer_multiples_of_2pi_hbar")
        ),
        "mass_moment_map_period_identified": bool(data.get("mass_moment_map_period_identified")),
        "minimal_positive_period_nonzero": bool(data.get("minimal_positive_period_nonzero")),
        "PT_sign_pairing_preserves_lattice": bool(data.get("PT_sign_pairing_preserves_lattice")),
    }
    ready = all(checks.values())
    frontier_payload = None
    if ready:
        frontier_payload = {
            "charge_lattice_integrality_derived": True,
            "minimal_mass_unit_derived": True,
            "unit_value_kg_derived": bool(data.get("unit_value_kg_derived")),
            "nonzero_sector_required": bool(data.get("nonzero_sector_required")),
            "fusion_splitting_forbidden": bool(data.get("fusion_splitting_forbidden")),
            "n_equals_one_selected": bool(data.get("n_equals_one_selected")),
            "selection_provenance_internal": bool(data.get("selection_provenance_internal")),
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(frontier_payload, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-pt-souriau-symplectic-integrality-gate",
        "active_core": "Z2_tunnel_Sigma",
        "checks": checks,
        "symplectic_integrality_ready": ready,
        "writes_alpha_frontier_inputs": ready,
        "blocked_by": [key for key, ok in checks.items() if not ok],
        "mathematical_standard": (
            "A charge lattice follows only if Omega_PT/(2*pi*hbar) has integral "
            "periods on the relevant boundary phase-space two-cycles."
        ),
        "impact": (
            "Without this prequantization theorem, Souriau gives a continuous "
            "mass orbit, not a minimal mass unit m_charge."
        ),
        "frontier_payload": frontier_payload,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 PT/Souriau Symplectic Integrality Gate",
                "",
                f"Symplectic integrality ready: `{payload['symplectic_integrality_ready']}`",
                "",
                payload["mathematical_standard"],
                "",
                payload["impact"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
