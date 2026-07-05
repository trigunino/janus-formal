from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
GRID_PATH = Path("outputs/active_z2_sigma/rsigma_a_grid_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/sigma_unit_frame_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_unit_throat_frame_input_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_unit_throat_frame_input_writer_gate.json")


def _load_active(path: Path, label: str) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{label} source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def _build_output(q_payload: dict, grid_payload: dict) -> dict:
    q = np.asarray(q_payload["unit_intrinsic_metric_q_ab"], dtype=float)
    grid = np.asarray(grid_payload["a_grid"], dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1] or not np.allclose(q, q.T):
        raise ValueError("unit_intrinsic_metric_q_ab must be symmetric square")
    if grid.ndim != 1 or len(grid) < 2 or np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    spatial_dim = q.shape[0]
    ambient_dim = spatial_dim + 2
    time_tangent = [1.0] + [0.0] * (ambient_dim - 1)
    spatial_tangents = []
    for i in range(spatial_dim):
        row = [0.0] * ambient_dim
        row[i + 1] = 1.0
        spatial_tangents.append(row)
    tangents = [time_tangent] + spatial_tangents
    normal_plus = [0.0] * ambient_dim
    normal_plus[-1] = 1.0
    normal_minus = [0.0] * ambient_dim
    normal_minus[-1] = -1.0
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "sigma_unit_frame_ready": True,
        "a_grid": grid.tolist(),
        "tangent_frames_plus": [tangents for _ in grid],
        "tangent_frames_minus": [tangents for _ in grid],
        "unit_normals_plus": [normal_plus for _ in grid],
        "unit_normals_minus": [normal_minus for _ in grid],
        "z2_orientation_sign": -1.0,
        "frame_provenance": "active unit throat chart; local frame only, not full embedding or K_ab",
        "full_embedding_claimed": False,
        "extrinsic_curvature_claimed": False,
    }


def build_payload(
    *,
    q_path: Path = Q_PATH,
    grid_path: Path = GRID_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "unit_intrinsic_metric_q_ab_inputs": q_path.exists(),
        "rsigma_a_grid_inputs": grid_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            output = _build_output(_load_active(q_path, "q_ab"), _load_active(grid_path, "a_grid"))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    missing = [key for key, exists in input_exists.items() if not exists]
    return {
        "status": "janus-z2-sigma-unit-throat-frame-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "sigma_unit_frame_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else (missing[0] if missing else "unit_throat_frame_validation"),
        "validation_error": validation_error,
        "scope": "local frame for u.n/e.n only; does not provide R_Sigma, X_pm, K_ab or full embedding",
        "next_required": []
        if output_written
        else [
            "derive_unit_intrinsic_metric_q_ab_inputs",
            "derive_active_a_grid_inputs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Unit Throat Frame Input Writer Gate",
        "",
        f"Frame written: `{payload['sigma_unit_frame_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Scope: `{payload['scope']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
