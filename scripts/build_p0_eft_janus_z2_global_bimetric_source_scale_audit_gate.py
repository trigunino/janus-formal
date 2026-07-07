from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_bimetric_source_scale_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_bimetric_source_scale_audit_gate.json"
)


def build_payload() -> dict:
    anchors = {
        "M15": {
            "role": "coupled field equations from a bimetric action",
            "scale_result": "requires dimensional stress tensors T_plus/T_minus",
            "absolute_scale_selected": False,
        },
        "M30": {
            "role": "modern bimetric/Souriau/PT formulation",
            "scale_result": "PT/Souriau fixes sign pairing, not mass magnitude",
            "absolute_scale_selected": False,
        },
        "topology_S4_to_RP4": {
            "role": "global Z2 projective cover and tunnel topology",
            "scale_result": "fixes cover ratio and sign transport only",
            "absolute_scale_selected": False,
        },
    }
    missing_inputs = [
        "dimensional_T_plus_or_T_minus_density_from_active_state",
        "global_Noether_or_Hamiltonian_mass_charge",
        "coadjoint_orbit_mass_invariant_with_state_selection",
        "compact_object_mass_parameter_from_active_bimetric_solution",
    ]
    return {
        "status": "janus-z2-global-bimetric-source-scale-audit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "anchors": anchors,
        "global_bimetric_equations_available": True,
        "Souriau_PT_sign_pairing_available": True,
        "absolute_mass_scale_found": False,
        "topology_only_scale_free": True,
        "missing_inputs": missing_inputs,
        "best_non_rustine_next": [
            "derive_dimensional_stress_energy_state_for_T_plus_T_minus",
            "derive_global_Noether_Hamiltonian_charge_or_orbit_mass",
            "then_write_null_bridge_global_mass_solution_inputs",
        ],
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global Bimetric Source Scale Audit Gate",
        "",
        f"Global bimetric equations available: `{payload['global_bimetric_equations_available']}`",
        f"Souriau/PT sign pairing available: `{payload['Souriau_PT_sign_pairing_available']}`",
        f"Absolute mass scale found: `{payload['absolute_mass_scale_found']}`",
        "",
        "## Missing Inputs",
    ]
    lines.extend(f"- `{item}`" for item in payload["missing_inputs"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
