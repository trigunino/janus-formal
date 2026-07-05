from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


Q_INPUT_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_radial_geometry_factors.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_geometry_factors_from_unit_q_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_geometry_factors_from_unit_q_gate.json"
)


def _reject_forbidden(payload: dict) -> None:
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


def _load_q(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("q_ab input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("q_ab input source must be active_derived")
    _reject_forbidden(payload)
    q = np.asarray(payload.get("unit_intrinsic_metric_q_ab"), dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1]:
        raise ValueError("unit_intrinsic_metric_q_ab must be a square matrix")
    if not np.all(np.isfinite(q)) or not np.allclose(q, q.T, atol=1e-12):
        raise ValueError("unit_intrinsic_metric_q_ab must be finite and symmetric")
    det_q = float(np.linalg.det(q))
    if det_q <= 0.0:
        raise ValueError("unit_intrinsic_metric_q_ab must have positive determinant")
    return {"dimension": int(q.shape[0]), "det_q": det_q}


def build_payload(
    *,
    q_input_path: Path = Q_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = q_input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            factors = _load_q(q_input_path)
            dim = factors["dimension"]
            sqrt_det_q = float(np.sqrt(factors["det_q"]))
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "fitted_counterterm_coefficient_used": False,
                "radial_metric_ansatz": "h_ab(R) = R_Sigma^2 q_ab",
                "dimension": dim,
                "det_unit_q": factors["det_q"],
                "sqrt_det_unit_q": sqrt_det_q,
                "sqrt_abs_h_formula": f"sqrt_abs_h(R) = R_Sigma^{dim} * sqrt_det_unit_q",
                "partial_R_sqrt_abs_h_formula": (
                    f"partial_R_sqrt_abs_h(R) = {dim} * R_Sigma^{dim - 1} * sqrt_det_unit_q"
                ),
                "requires_R_Sigma_of_a_for_values": True,
                "requires_L_ct_and_partial_R_L_ct_for_E_counterterm": True,
                "geometry_factors_ready": True,
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-radial-geometry-factors-from-unit-q-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(q_input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "counterterm_radial_geometry_factors_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_unit_intrinsic_metric_q_ab_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else ["derive_unit_intrinsic_metric_q_ab_inputs_json"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Radial Geometry Factors From Unit q Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['counterterm_radial_geometry_factors_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
