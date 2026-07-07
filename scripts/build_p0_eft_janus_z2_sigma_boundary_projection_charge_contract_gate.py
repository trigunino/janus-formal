from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "active_z2_sigma_boundary_projection.json"
PROJECTED_OUTPUT_PATH = BASE / "projected_boundary_charge_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_boundary_projection_charge_contract_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_boundary_projection_charge_contract_gate.json"
)

REQUIRED_FIELDS = [
    "active_core",
    "k",
    "a_grid",
    "R_Sigma_abs_m",
    "Q_boundary_raw",
    "Q_reference_raw",
    "V_eff_m3",
    "kappa_Z2Sigma",
    "reference_type",
    "Q_reference_zero_on_reference",
    "Q_raw_kind",
    "C_BY",
    "action_signature",
    "provenance",
]

FORBIDDEN_PROVENANCE_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "observational_H0_fit_used",
    "fitted_density_used",
]

C_SI = 299_792_458.0


def _read_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _finite_number(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value))


def _finite_array(value: Any) -> bool:
    return isinstance(value, list) and bool(value) and all(_finite_number(v) for v in value)


def _missing_fields(payload: dict[str, Any]) -> list[str]:
    return [field for field in REQUIRED_FIELDS if field not in payload]


def _validate(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    missing = _missing_fields(payload)
    if missing:
        return [f"missing_fields:{','.join(missing)}"]

    if payload["active_core"] != "Z2_tunnel_Sigma":
        errors.append("active_core_must_be_Z2_tunnel_Sigma")
    if payload["reference_type"] not in ["Minkowski", "Milne", "isometric_reference"]:
        errors.append("reference_type_must_be_Minkowski_Milne_or_isometric_reference")
    if payload["Q_raw_kind"] not in ["mass_kg", "energy_J"]:
        errors.append("Q_raw_kind_must_be_mass_kg_or_energy_J")
    if payload["Q_reference_zero_on_reference"] is not True:
        errors.append("Q_reference_zero_on_reference_must_be_true")

    provenance = payload.get("provenance")
    if not isinstance(provenance, dict):
        errors.append("provenance_must_be_object")
    else:
        for flag in FORBIDDEN_PROVENANCE_FLAGS:
            if provenance.get(flag) is True:
                errors.append(f"forbidden_provenance:{flag}")

    arrays = ["a_grid", "Q_boundary_raw", "Q_reference_raw", "V_eff_m3"]
    for name in arrays:
        if not _finite_array(payload[name]):
            errors.append(f"{name}_must_be_nonempty_finite_array")
    if all(_finite_array(payload[name]) for name in arrays):
        lengths = {len(payload[name]) for name in arrays}
        if len(lengths) != 1:
            errors.append("a_grid_Q_boundary_Q_reference_V_eff_lengths_must_match")
        if any(float(v) <= 0.0 for v in payload["a_grid"]):
            errors.append("a_grid_must_be_positive")
        if any(float(v) <= 0.0 for v in payload["V_eff_m3"]):
            errors.append("V_eff_m3_must_be_positive")

    for name in ["R_Sigma_abs_m", "kappa_Z2Sigma", "C_BY"]:
        if not _finite_number(payload[name]) or float(payload[name]) <= 0.0:
            errors.append(f"{name}_must_be_positive_finite")
    if payload["k"] not in [-1, 0, 1]:
        errors.append("k_must_be_-1_0_or_1")

    return errors


def _reduce_projected_charge(payload: dict[str, Any]) -> dict[str, Any]:
    q_ren = [
        float(q) - float(q0)
        for q, q0 in zip(payload["Q_boundary_raw"], payload["Q_reference_raw"])
    ]
    c_by = float(payload["C_BY"])
    if payload["Q_raw_kind"] == "energy_J":
        q_energy_j = [c_by * q for q in q_ren]
        q_mass_kg = [q / (C_SI * C_SI) for q in q_energy_j]
    else:
        q_mass_kg = [c_by * q for q in q_ren]
        q_energy_j = [q * C_SI * C_SI for q in q_mass_kg]
    rho_eff_kg_m3 = [
        q / float(volume) for q, volume in zip(q_mass_kg, payload["V_eff_m3"])
    ]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "BrownYork_boundary_projection_reference_subtraction",
        "reference_type": payload["reference_type"],
        "action_signature": payload["action_signature"],
        "k": payload["k"],
        "a_grid": payload["a_grid"],
        "R_Sigma_abs_m": payload["R_Sigma_abs_m"],
        "kappa_Z2Sigma": payload["kappa_Z2Sigma"],
        "Q_raw_kind": payload["Q_raw_kind"],
        "C_BY": payload["C_BY"],
        "Q_ren_raw": q_ren,
        "Q_boundary_mass_kg": q_mass_kg,
        "Q_boundary_energy_J": q_energy_j,
        "V_eff_m3": payload["V_eff_m3"],
        "rho_eff_kg_m3": rho_eff_kg_m3,
        "Q_reference_zero_on_reference": True,
        "projected_boundary_charge_ready": True,
        "forbidden_shortcuts_absent": True,
    }


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    projected_output_path: Path = PROJECTED_OUTPUT_PATH,
    write_projected: bool = False,
) -> dict[str, Any]:
    raw = _read_json(input_path)
    input_exists = raw is not None
    validation_errors = [] if raw is None else _validate(raw)
    reduction = None
    if raw is not None and not validation_errors:
        reduction = _reduce_projected_charge(raw)
        if write_projected:
            projected_output_path.parent.mkdir(parents=True, exist_ok=True)
            projected_output_path.write_text(
                json.dumps(reduction, indent=2), encoding="utf-8"
            )

    ready = reduction is not None
    return {
        "status": "janus-z2-sigma-boundary-projection-charge-contract-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "B_BrownYork_quasilocal_reference_projection",
        "input_path": str(input_path),
        "projected_output_path": str(projected_output_path),
        "contract_declared": True,
        "required_fields": REQUIRED_FIELDS,
        "forbidden_provenance_flags": FORBIDDEN_PROVENANCE_FLAGS,
        "input_exists": input_exists,
        "validation_errors": validation_errors,
        "projection_charge_inputs_available": ready,
        "Q_ren_computable": ready,
        "rho_eff_boundary_computable": ready,
        "projected_boundary_charge_ready": ready,
        "writes_projected_boundary_charge_inputs": ready and write_projected,
        "reduction": reduction,
        "full_no_fit_cosmology_ready": False,
        "forbidden_shortcuts": [
            "do_not_insert_fitted_density",
            "do_not_set_Q_reference_by_H0_fit",
            "do_not_reuse_archived_Z4_charge",
            "do_not_use_compressed_Planck_LCDM_background",
        ],
        "next_required": []
        if ready
        else [
            "provide_active_z2_sigma_boundary_projection_json",
            "derive_Q_boundary_raw_from_theta_e_omega_projection",
            "derive_Q_reference_raw_on_same_surface",
            "derive_absolute_RSigma_and_V_eff",
        ],
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_projected=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Projection Charge Contract Gate",
        "",
        f"Route: `{payload['route']}`",
        f"Input exists: `{payload['input_exists']}`",
        f"Projected boundary charge ready: `{payload['projected_boundary_charge_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Required Input",
    ]
    lines.extend(f"- `{field}`" for field in REQUIRED_FIELDS)
    if payload["validation_errors"]:
        lines.extend(["", "## Validation Errors"])
        lines.extend(f"- `{error}`" for error in payload["validation_errors"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
