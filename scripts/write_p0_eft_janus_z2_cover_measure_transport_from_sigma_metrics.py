from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np


INPUT_PATH = Path("outputs/active_z2_sigma/sector_metric_on_sigma_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_cover/measure_transport_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_measure_transport_from_sigma_metrics.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_measure_transport_from_sigma_metrics.json")


def _sqrt_abs_det(matrix: np.ndarray) -> float:
    det = float(np.linalg.det(matrix))
    if not math.isfinite(det) or det == 0.0:
        raise ValueError("metric determinant must be finite and nonzero")
    return math.sqrt(abs(det))


def build_payload(input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-cover-measure-transport-from-sigma-metrics",
            "input_path": str(input_path),
            "output_path": str(output_path),
            "input_manifest_present": False,
            "writes_active_manifest": False,
            "gate_passed": False,
            "primary_blocker": "sector_metric_on_sigma_inputs_missing",
        }
    source = json.loads(input_path.read_text(encoding="utf-8"))
    if source.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("source active_core must be Z2_tunnel_Sigma")
    for flag in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if source.get(flag) is not False:
            raise ValueError(f"{flag} must be false")

    plus = np.asarray(source["metric_plus_munu_values"], dtype=float)
    minus = np.asarray(source["metric_minus_munu_values"], dtype=float)
    if plus.shape != minus.shape or plus.ndim != 3 or plus.shape[1] != plus.shape[2]:
        raise ValueError("metric arrays must have shape [grid,d,d]")
    grid = np.asarray(source["a_grid"], dtype=float)
    if grid.shape != (plus.shape[0],):
        raise ValueError("a_grid must align with metric arrays")

    manifest = {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "active_cover_metric_determinants",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "full_no_fit_prediction_ready": False,
        "parameter_grid": grid.tolist(),
        "sqrt_abs_g_plus": [_sqrt_abs_det(row) for row in plus],
        "sqrt_abs_g_minus": [_sqrt_abs_det(row) for row in minus],
        "tau_jacobian_abs_minus_to_plus": [1.0 for _ in grid],
        "tau_jacobian_abs_plus_to_minus": [1.0 for _ in grid],
        "restriction": "local_sigma_metric_restriction",
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-cover-measure-transport-from-sigma-metrics",
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_manifest_present": True,
        "writes_active_manifest": True,
        "local_sigma_restriction_only": True,
        "gate_passed": True,
        "full_no_fit_prediction_ready": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Cover Measure Transport From Sigma Metrics",
                "",
                f"Input present: `{payload['input_manifest_present']}`",
                f"Writes active manifest: `{payload['writes_active_manifest']}`",
                f"Local Sigma restriction only: `{payload.get('local_sigma_restriction_only', False)}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
