from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_embedding_geometry_manifest import (
    load_active_z2sigma_embedding_geometry_manifest,
)
from janus_lab.z2_sigma_metric_geometry import (
    tangent_normal_contractions,
    vector_normal_contractions,
)


METRIC_PATH = Path("outputs/active_z2_sigma/sector_metric_on_sigma_inputs.json")
VELOCITY_PATH = Path("outputs/active_z2_sigma/sector_four_velocity_on_sigma_inputs.json")
EMBEDDING_PATH = Path("outputs/active_z2_sigma/active_tunnel_embedding_geometry_inputs.json")
UNIT_FRAME_PATH = Path("outputs/active_z2_sigma/sigma_unit_frame_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/flow_tangency_on_sigma_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flow_tangency_from_embedding_velocity_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flow_tangency_from_embedding_velocity_gate.json")

FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "archived_z4_background_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
]


def _reject_forbidden(payload: dict) -> None:
    for key in FORBIDDEN_FLAGS:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _load_active(path: Path, label: str, ready_key: str) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{label} source must be active_derived")
    if payload.get(ready_key) is not True:
        raise ValueError(f"{ready_key} must be true")
    _reject_forbidden(payload)
    return payload


def _grid(payload: dict, label: str) -> np.ndarray:
    grid = np.asarray(payload["a_grid"], dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError(f"{label} a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError(f"{label} a_grid must be positive and strictly increasing")
    return grid


def _aligned(reference: np.ndarray, payload: dict, label: str) -> None:
    grid = _grid(payload, label)
    if grid.shape != reference.shape or not np.allclose(grid, reference, rtol=0.0, atol=0.0):
        raise ValueError(f"{label} a_grid must match exactly")


def _build_output(metric: dict, velocity: dict, embedding: dict, *, tolerance: float) -> dict:
    grid = _grid(metric, "metric")
    _aligned(grid, velocity, "velocity")
    _aligned(grid, embedding, "embedding")
    u_dot_n_plus = vector_normal_contractions(
        metric["metric_plus_munu_values"],
        velocity["u_plus_contravariant_values"],
        embedding["unit_normals_plus"],
    )
    u_dot_n_minus = vector_normal_contractions(
        metric["metric_minus_munu_values"],
        velocity["u_minus_contravariant_values"],
        embedding["unit_normals_minus"],
    )
    e_dot_n_plus = tangent_normal_contractions(
        metric["metric_plus_munu_values"],
        embedding["tangent_frames_plus"],
        embedding["unit_normals_plus"],
    )
    e_dot_n_minus = tangent_normal_contractions(
        metric["metric_minus_munu_values"],
        embedding["tangent_frames_minus"],
        embedding["unit_normals_minus"],
    )
    max_abs = max(
        float(np.max(np.abs(np.asarray(u_dot_n_plus, dtype=float)))),
        float(np.max(np.abs(np.asarray(u_dot_n_minus, dtype=float)))),
        float(np.max(np.abs(np.asarray(e_dot_n_plus, dtype=float)))),
        float(np.max(np.abs(np.asarray(e_dot_n_minus, dtype=float)))),
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
        "flow_tangency_on_sigma_ready": max_abs <= tolerance,
        "a_grid": grid.tolist(),
        "u_dot_n_plus_values": u_dot_n_plus,
        "u_dot_n_minus_values": u_dot_n_minus,
        "e_dot_n_plus_values": e_dot_n_plus,
        "e_dot_n_minus_values": e_dot_n_minus,
        "tolerance": tolerance,
        "max_abs_contraction": max_abs,
        "formula": "u.n=0 and e_a.n=0",
        "frame_source_scope": embedding.get("frame_provenance", embedding.get("embedding_provenance", "active embedding geometry")),
        "full_embedding_claimed": bool(embedding.get("full_embedding_claimed", True)),
    }


def build_payload(
    *,
    metric_path: Path = METRIC_PATH,
    velocity_path: Path = VELOCITY_PATH,
    embedding_path: Path = EMBEDDING_PATH,
    unit_frame_path: Path = UNIT_FRAME_PATH,
    output_path: Path = OUTPUT_PATH,
    tolerance: float = 1.0e-10,
) -> dict:
    input_exists = {
        "sector_metric_on_sigma_inputs": metric_path.exists(),
        "sector_four_velocity_on_sigma_inputs": velocity_path.exists(),
        "active_tunnel_embedding_geometry_inputs": embedding_path.exists(),
        "sigma_unit_frame_inputs": unit_frame_path.exists(),
    }
    frame_path = embedding_path if embedding_path.exists() else unit_frame_path
    frame_label = (
        "active_tunnel_embedding_geometry_inputs"
        if embedding_path.exists()
        else "sigma_unit_frame_inputs"
    )
    output_written = False
    validation_error = None
    ready = False
    if input_exists["sector_metric_on_sigma_inputs"] and input_exists["sector_four_velocity_on_sigma_inputs"] and frame_path.exists():
        try:
            frame = (
                load_active_z2sigma_embedding_geometry_manifest(frame_path)
                if frame_label == "active_tunnel_embedding_geometry_inputs"
                else _load_active(frame_path, "unit frame", "sigma_unit_frame_ready")
            )
            output = _build_output(
                _load_active(metric_path, "metric", "sector_metric_on_sigma_ready"),
                _load_active(velocity_path, "velocity", "sector_four_velocity_on_sigma_ready"),
                frame,
                tolerance=tolerance,
            )
            output["frame_source"] = frame_label
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
            ready = bool(output["flow_tangency_on_sigma_ready"])
        except Exception as exc:
            validation_error = str(exc)
    missing = [
        key for key, exists in input_exists.items()
        if not exists and key not in {"active_tunnel_embedding_geometry_inputs", "sigma_unit_frame_inputs"}
    ]
    if not embedding_path.exists() and not unit_frame_path.exists():
        missing.append("active_tunnel_embedding_geometry_inputs_or_sigma_unit_frame_inputs")
    return {
        "status": "janus-z2-sigma-flow-tangency-from-embedding-velocity-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "flow_tangency_written": output_written,
        "flow_tangency_ready": ready,
        "gate_passed": output_written and ready,
        "primary_blocker": "none" if output_written and ready else (missing[0] if missing else "flow_tangency_validation"),
        "validation_error": validation_error,
        "next_required": []
        if output_written and ready
        else [
            "derive_sector_metric_on_sigma_inputs",
            "derive_sector_four_velocity_on_sigma_inputs",
            "derive_active_tunnel_embedding_geometry_inputs_or_sigma_unit_frame_inputs",
            "verify_u_dot_n_and_e_dot_n_zero",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Flow Tangency From Embedding/Velocity Gate",
        "",
        f"Output written: `{payload['flow_tangency_written']}`",
        f"Ready: `{payload['flow_tangency_ready']}`",
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
