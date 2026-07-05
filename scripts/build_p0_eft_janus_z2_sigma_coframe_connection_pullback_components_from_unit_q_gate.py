from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


INPUT_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/coframe_connection_pullback_components_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coframe_connection_pullback_components_from_unit_q_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coframe_connection_pullback_components_from_unit_q_gate.json")


def _load_q(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("q_ab active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("q_ab source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    q = np.asarray(payload.get("unit_intrinsic_metric_q_ab"), dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1]:
        raise ValueError("unit_intrinsic_metric_q_ab must be square")
    if not np.all(np.isfinite(q)):
        raise ValueError("unit_intrinsic_metric_q_ab must be finite")
    if not np.allclose(q, q.T, atol=1e-10):
        raise ValueError("unit_intrinsic_metric_q_ab must be symmetric")
    if abs(float(np.linalg.det(q))) < 1e-14:
        raise ValueError("unit_intrinsic_metric_q_ab must be nondegenerate")
    return payload


def _orthonormal_coframe(q: np.ndarray) -> np.ndarray:
    # q = L L^T, so e = L^T has e^T e = q in Euclidean internal gauge.
    return np.linalg.cholesky(q).T


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            source = _load_q(input_path)
            q = np.asarray(source["unit_intrinsic_metric_q_ab"], dtype=float)
            n = q.shape[0]
            coframe = _orthonormal_coframe(q)
            zero_2form = np.zeros((n, n, n), dtype=float)
            zero_connection = np.zeros((n, n, n), dtype=float)
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "coframe_pullback_ready": True,
                "spin_connection_pullback_ready": True,
                "exterior_derivative_coframe_ready": True,
                "selected_route": "cartan_first_structure_equation",
                "coframe_connection_route": "torsionless_unit_orthonormal_chart",
                "torsionless_baseline_only": True,
                "q_ab": q.tolist(),
                "coframe_e_I_a": coframe.tolist(),
                "exterior_de_I_ab": zero_2form.tolist(),
                "spin_connection_omega_IJ_a": zero_connection.tolist(),
                "provenance": (
                    "local orthonormal Sigma/RP3 chart from unit_intrinsic_metric_q_ab; "
                    "torsionless baseline, not a nonzero Holst torsion solution"
                ),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-coframe-connection-pullback-components-from-unit-q-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "coframe_connection_pullback_components_written": output_written,
        "torsionless_baseline_only": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "unit_intrinsic_metric_q_ab_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_unit_intrinsic_metric_q_ab_for_projective_throat",
            "write_outputs_active_z2_sigma_unit_intrinsic_metric_q_ab_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coframe/Connection Pullback Components From Unit q Gate",
        "",
        f"Output written: `{payload['coframe_connection_pullback_components_written']}`",
        f"Torsionless baseline only: `{payload['torsionless_baseline_only']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
