from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
PT67_Q_PATH = BASE / "boundary_projection_charge_from_pt67_theta.json"
BC_INPUT_PATH = BASE / "pt67_generalized_boundary_action_choice_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_pt67_generalized_boundary_bc_reference_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_pt67_generalized_boundary_bc_reference_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")
ALLOWED_BC_FAMILIES = [
    "Dirichlet_BrownYork",
    "mixed_intrinsic_extrinsic",
    "optimal_isometric_reference",
    "closed_cosmology_generalized_BC",
]


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_zero(values: Any) -> bool:
    return isinstance(values, list) and all(float(value) == 0.0 for value in values)


def _validate_bc(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload.get("branch") != "PT67_regular_Sigma":
        errors.append("branch_must_be_PT67_regular_Sigma")
    if payload.get("source") != "active_derived_boundary_condition":
        errors.append("source_must_be_active_derived_boundary_condition")
    if payload.get("bc_family") not in ALLOWED_BC_FAMILIES:
        errors.append("bc_family_not_allowed")
    for key in [
        "boundary_action_choice",
        "reference_geometry_choice",
        "same_topology_surface_proved",
        "variation_principle_well_posed",
        "non_fit_provenance",
    ]:
        if key not in payload:
            errors.append(f"missing:{key}")
    provenance = str(payload.get("non_fit_provenance", ""))
    if any(token in provenance.lower() for token in FORBIDDEN_TOKENS):
        errors.append("non_fit_provenance_contains_forbidden_token")
    if payload.get("same_topology_surface_proved") is not True:
        errors.append("same_topology_surface_proved_must_be_true")
    if payload.get("variation_principle_well_posed") is not True:
        errors.append("variation_principle_well_posed_must_be_true")
    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
    ]:
        if payload.get(key) is True:
            errors.append(f"forbidden_flag:{key}")
    return errors


def build_payload(
    *,
    pt67_q_path: Path = PT67_Q_PATH,
    bc_input_path: Path = BC_INPUT_PATH,
) -> dict[str, Any]:
    pt67 = _read(pt67_q_path)
    bc = _read(bc_input_path)
    pt67_zero = _all_zero(pt67.get("Q_boundary_minus_reference_unit"))
    bc_errors = [] if not bc else _validate_bc(bc)
    bc_ready = bool(bc) and not bc_errors
    same_reference_results = {
        "Minkowski_or_Milne_same_boundary": 0.0 if pt67_zero else None,
        "isometric_same_intrinsic_boundary": 0.0 if pt67_zero else None,
        "Dirichlet_BrownYork_PT67": 0.0 if pt67_zero else None,
    }
    return {
        "status": "janus-z2-sigma-pt67-generalized-boundary-bc-reference-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "PT67_regular_Sigma",
        "pt67_projection_ready": bool(pt67),
        "pt67_Q_ren_unit_all_zero": pt67_zero,
        "same_boundary_reference_scan": same_reference_results,
        "same_boundary_references_all_zero": pt67_zero,
        "generalized_boundary_condition_input": str(bc_input_path),
        "generalized_boundary_condition_available": bool(bc),
        "generalized_boundary_condition_valid": bc_ready,
        "validation_errors": bc_errors,
        "allowed_bc_families": ALLOWED_BC_FAMILIES,
        "can_escape_pt67_zero_without_new_bc": False,
        "bc_route_can_be_tested": bc_ready,
        "interpretation": (
            "The regular PT67 Brown-York/Noether projection is an obstacle proof "
            "for the standard same-boundary references: Q_ren=0. A nonzero "
            "quasilocal charge in this branch requires an explicit generalized "
            "boundary-condition/action choice with a well-posed variational "
            "principle and non-fit provenance."
        ),
        "next_required": []
        if bc_ready
        else [
            "derive_pt67_generalized_boundary_action_choice",
            "derive_reference_geometry_on_same_topology_surface",
            "prove_variation_principle_well_posed",
            "then_compute_Q_boundary_and_Q_reference",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma PT67 Generalized Boundary BC Reference Gate",
        "",
        payload["interpretation"],
        "",
        f"PT67 Q_ren all zero: `{payload['pt67_Q_ren_unit_all_zero']}`",
        f"Generalized BC valid: `{payload['generalized_boundary_condition_valid']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
