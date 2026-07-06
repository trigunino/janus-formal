from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_reference_subtraction_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_reference_subtraction_gate.json"
)


def build_payload() -> dict:
    closure = {
        "Hamiltonian_volume_part_on_shell_constraint": True,
        "Hamiltonian_value_carried_by_boundary_term": True,
        "Holst_NiehYan_no_independent_bulk_or_sigma_density": True,
        "quasilocal_reference_subtraction_declared": True,
        "reference_vacuum_zero_energy_condition_declared": True,
        "physical_boundary_charge_magnitude_available": False,
        "H0_Z2Sigma_numeric_ready": False,
    }
    return {
        "status": "janus-z2-sigma-boundary-reference-subtraction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "Hamiltonian_boundary_reference_normalization",
        "bibliography_basis": [
            "Holst boundary terms: Corichi-Wilson-Ewing 2010",
            "first-order boundary/topological terms: Corichi-Rubalcava-Garcia-Vukasinac 2016",
            "Hamiltonian boundary charges: Corichi-Reyes 2015 and Chen-Nester boundary reference",
            "Brown-York quasilocal subtraction for cosmology: Brown-York 1993, Epp 2009/2021",
        ],
        "reference_policy": (
            "Choose the quasilocal Hamiltonian subtraction so the reference "
            "vacuum branch, Minkowski/Milne according to the active slicing, "
            "has zero boundary energy."
        ),
        "closure": closure,
        "zero_point_fixed": True,
        "new_sigma_density_introduced": False,
        "ready_for_H0_normalization": False,
        "remaining_frontier": (
            "The additive zero is fixed, but the active Z2/Sigma boundary charge "
            "above the reference vacuum is still not derived."
        ),
        "forbidden_shortcuts": [
            "do_not_add_independent_sigma_density",
            "do_not_use_Holst_or_NiehYan_as_new_surface_energy",
            "do_not_set_H0_from_reference_zero_condition_alone",
            "do_not_use_observational_H0_fit",
        ],
        "next_required": [
            "derive_BrownYork_or_first_order_boundary_charge_for_active_Z2Sigma_branch",
            "evaluate_charge_above_Minkowski_or_Milne_reference",
            "map_boundary_charge_to_H0_Z2Sigma_normalization",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Reference Subtraction Gate",
        "",
        payload["reference_policy"],
        "",
        f"Zero point fixed: `{payload['zero_point_fixed']}`",
        f"New Sigma density introduced: `{payload['new_sigma_density_introduced']}`",
        f"Ready for H0 normalization: `{payload['ready_for_H0_normalization']}`",
        "",
        "## Remaining Frontier",
        payload["remaining_frontier"],
        "",
        "## Closure",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closure"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
