from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


COEFF_PATH = Path("outputs/active_z2_sigma/counterterm_minimal_basis_coefficients.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_lct_radial_profile.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_profile_from_minimal_coefficients_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_profile_from_minimal_coefficients_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _active(payload: dict) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("coefficient active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("coefficient source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "fitted_counterterm_coefficient_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _array(payload: dict, key: str, shape: tuple[int, ...]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite and aligned")
    return values


def _build_profile(coeff: dict) -> dict:
    _active(coeff)
    grid = np.asarray(coeff["a_grid"], dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    radius = _array(coeff, "R_Sigma_values", grid.shape)
    if np.any(radius <= 0.0):
        raise ValueError("R_Sigma_values must be positive")
    c1 = _array(coeff, "c1_values", grid.shape)
    c2 = _array(coeff, "c2_values", grid.shape)
    c3 = _array(coeff, "c3_values", grid.shape)
    eps = float(coeff.get("z2_orientation_sign", 1.0))
    if eps not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")
    k = 3.0 / radius
    intrinsic_r = 6.0 / radius**2
    L_ct = c1 * eps * k + c2 * k**2 + c3 * intrinsic_r
    partial_R_L_ct = (
        -3.0 * c1 * eps / radius**2
        - 18.0 * c2 / radius**3
        - 12.0 * c3 / radius**3
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "L_ct_profile_ready": True,
        "a_grid": grid.tolist(),
        "R_Sigma_values": radius.tolist(),
        "L_ct_values": L_ct.tolist(),
        "partial_R_L_ct_values": partial_R_L_ct.tolist(),
        "L_ct_expression": "c1*(epsilon_Z2*K_trace) + c2*K_trace^2 + c3*R_intrinsic",
        "partial_R_L_ct_convention": "coefficient_values_held_fixed_under_local_radial_variation",
        "coefficient_source": "counterterm_minimal_basis_coefficients",
        "coefficient_status": coeff.get("coefficient_status", "unknown"),
    }


def build_payload(
    *,
    coeff_path: Path = COEFF_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = coeff_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            output = _build_profile(_load(coeff_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-lct-profile-from-minimal-coefficients-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(coeff_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "L_ct_profile_from_coefficients_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "counterterm_minimal_basis_coefficients",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "write_counterterm_trace_residual_inputs_json",
            "run_counterterm_minimal_basis_coefficient_solver_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm L_ct Profile From Minimal Coefficients Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
