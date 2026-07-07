from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_pt67_generalized_boundary_bc_reference_gate import (
    build_payload as build_bc_reference,
)


BASE = Path("outputs/active_z2_sigma")
BC_INPUT_PATH = BASE / "pt67_generalized_boundary_action_choice_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_pt67_generalized_boundary_action_reduction_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_pt67_generalized_boundary_action_reduction_gate.json"
)

COEFFICIENTS = ["lambda_0", "lambda_R3", "lambda_K", "lambda_K2", "lambda_Kab2"]
SCALARS = [
    "volume_factor_pi2_R3",
    "R3_coeff_over_R2",
    "K_trace_coeff_over_inv_R",
    "K2_coeff_over_inv_R2",
    "Kab2_coeff_over_inv_R2",
]


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _finite_number(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value))


def _extract_coefficients(payload: dict[str, Any]) -> tuple[dict[str, float], list[str]]:
    errors: list[str] = []
    raw = payload.get("boundary_density_coefficients")
    if not isinstance(raw, dict):
        return {}, ["missing:boundary_density_coefficients"]
    coeffs: dict[str, float] = {}
    for key in COEFFICIENTS:
        value = raw.get(key)
        if not _finite_number(value):
            errors.append(f"{key}_must_be_finite")
        else:
            coeffs[key] = float(value)
    if payload.get("coefficient_status") != "derived_not_fitted":
        errors.append("coefficient_status_must_be_derived_not_fitted")
    return coeffs, errors


def _extract_scalars(payload: dict[str, Any], name: str) -> tuple[dict[str, float], list[str]]:
    errors: list[str] = []
    raw = payload.get(name)
    if not isinstance(raw, dict):
        return {}, [f"missing:{name}"]
    scalars: dict[str, float] = {}
    for key in SCALARS:
        value = raw.get(key)
        if not _finite_number(value):
            errors.append(f"{name}.{key}_must_be_finite")
        else:
            scalars[key] = float(value)
    return scalars, errors


def _polynomial_terms(coeffs: dict[str, float], scalars: dict[str, float]) -> dict[str, float]:
    volume = scalars["volume_factor_pi2_R3"]
    return {
        "pi2_R3": volume * coeffs["lambda_0"],
        "pi2_R2": volume
        * coeffs["lambda_K"]
        * scalars["K_trace_coeff_over_inv_R"],
        "pi2_R1": volume
        * (
            coeffs["lambda_R3"] * scalars["R3_coeff_over_R2"]
            + coeffs["lambda_K2"] * scalars["K2_coeff_over_inv_R2"]
            + coeffs["lambda_Kab2"] * scalars["Kab2_coeff_over_inv_R2"]
        ),
    }


def _subtract_terms(a: dict[str, float], b: dict[str, float]) -> dict[str, float]:
    return {key: a[key] - b[key] for key in ["pi2_R3", "pi2_R2", "pi2_R1"]}


def build_payload(*, bc_input_path: Path = BC_INPUT_PATH) -> dict[str, Any]:
    bc_status = build_bc_reference(bc_input_path=bc_input_path)
    payload = _read(bc_input_path)
    coeffs, coeff_errors = _extract_coefficients(payload)
    boundary, boundary_errors = _extract_scalars(payload, "boundary_geometry_scalars")
    reference, reference_errors = _extract_scalars(payload, "reference_geometry_scalars")
    errors = (
        list(bc_status["validation_errors"])
        + coeff_errors
        + boundary_errors
        + reference_errors
    )
    ready = bc_status["generalized_boundary_condition_valid"] and not errors
    reduction = None
    if ready:
        boundary_terms = _polynomial_terms(coeffs, boundary)
        reference_terms = _polynomial_terms(coeffs, reference)
        q_ren_terms = _subtract_terms(boundary_terms, reference_terms)
        nonzero = any(abs(value) > 0.0 for value in q_ren_terms.values())
        reduction = {
            "density_model": "L_B = lambda_0 + lambda_R3 R3 + lambda_K K + lambda_K2 K^2 + lambda_Kab2 K_ab K^ab",
            "Q_boundary_polynomial_pi2_units": boundary_terms,
            "Q_reference_polynomial_pi2_units": reference_terms,
            "Q_ren_polynomial_pi2_units": q_ren_terms,
            "Q_ren_symbolic": (
                f"pi^2*({q_ren_terms['pi2_R3']} R^3 + "
                f"{q_ren_terms['pi2_R2']} R^2 + {q_ren_terms['pi2_R1']} R)"
            ),
            "Q_ren_symbolically_nonzero": nonzero,
            "absolute_RSigma_still_required": nonzero,
        }
    return {
        "status": "janus-z2-sigma-pt67-generalized-boundary-action-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "PT67_regular_Sigma",
        "bc_reference_gate": {
            "status": bc_status["status"],
            "valid": bc_status["generalized_boundary_condition_valid"],
            "same_boundary_standard_zero": bc_status["same_boundary_references_all_zero"],
        },
        "input_path": str(bc_input_path),
        "input_exists": bool(payload),
        "validation_errors": errors,
        "reduction_ready": ready,
        "reduction": reduction,
        "can_write_numeric_Q_boundary_raw": bool(
            reduction and not reduction["absolute_RSigma_still_required"]
        ),
        "next_required": []
        if ready
        else [
            "derive_generalized_boundary_density_coefficients",
            "derive_boundary_and_reference_geometry_scalars",
            "keep_coefficient_status_derived_not_fitted",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma PT67 Generalized Boundary Action Reduction Gate",
        "",
        f"Reduction ready: `{payload['reduction_ready']}`",
        f"Can write numeric Q_boundary_raw: `{payload['can_write_numeric_Q_boundary_raw']}`",
    ]
    if payload["reduction"]:
        lines.extend(["", f"Q_ren: `{payload['reduction']['Q_ren_symbolic']}`"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
