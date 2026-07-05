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


EMBEDDING_PATH = Path("outputs/active_z2_sigma/active_tunnel_embedding_geometry_inputs.json")
STRESS_PATH = Path("outputs/active_z2_sigma/bulk_stress_on_sigma_inputs.json")
RADIAL_WEIGHTS_PATH = Path("outputs/active_z2_sigma/radial_variation_tangent_weights_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_projection_components.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_matter_flux_projection_components_from_embedding_stress_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_matter_flux_projection_components_from_embedding_stress_gate.json"
)


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


def _load_active_payload(path: Path, label: str) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{label} source must be active_derived")
    _reject_forbidden(payload)
    return payload


def _grid(payload: dict, label: str) -> np.ndarray:
    grid = np.asarray(payload["a_grid"], dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError(f"{label} a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError(f"{label} a_grid must be positive and strictly increasing")
    return grid


def _aligned_grid(reference: np.ndarray, payload: dict, label: str) -> None:
    grid = _grid(payload, label)
    if grid.shape != reference.shape or not np.allclose(grid, reference, rtol=0.0, atol=0.0):
        raise ValueError(f"{label} a_grid must match embedding a_grid exactly")


def _normal_array(values: object, n_grid: int) -> np.ndarray:
    normals = np.asarray(values, dtype=float)
    if normals.ndim == 3 and normals.shape[1] == 1:
        normals = normals[:, 0, :]
    if normals.ndim != 2 or normals.shape[0] != n_grid:
        raise ValueError("unit normals must have shape [len(a_grid), dim] or [len(a_grid), 1, dim]")
    return normals


def _build_output(embedding: dict, stress: dict, radial: dict) -> dict:
    grid = _grid(embedding, "embedding")
    _aligned_grid(grid, stress, "stress")
    _aligned_grid(grid, radial, "radial weights")

    tangents = np.asarray(embedding["tangent_frames_plus"], dtype=float)
    T_plus = np.asarray(stress["T_plus_munu_values"], dtype=float)
    T_minus = np.asarray(stress["T_minus_munu_values"], dtype=float)
    normal_plus = _normal_array(embedding["unit_normals_plus"], len(grid))
    normal_minus = _normal_array(embedding["unit_normals_minus"], len(grid))
    radial_weights = np.asarray(radial["radial_variation_tangent_weights"], dtype=float)

    if tangents.ndim != 3 or tangents.shape[0] != len(grid):
        raise ValueError("tangent_frames_plus must have shape [len(a_grid), n_tangent, dim]")
    if T_plus.shape != T_minus.shape or T_plus.ndim != 3 or T_plus.shape[0] != len(grid):
        raise ValueError("T_plus/minus must have shape [len(a_grid), dim, dim]")
    dim = T_plus.shape[1]
    if T_plus.shape[2] != dim:
        raise ValueError("T_plus/minus tensors must be square")
    if tangents.shape[2] != dim or normal_plus.shape[1] != dim or normal_minus.shape[1] != dim:
        raise ValueError("stress, tangents and normals dimensions must agree")
    if radial_weights.shape != (len(grid), tangents.shape[1]):
        raise ValueError("radial_variation_tangent_weights must match [len(a_grid), n_tangent]")
    for name, array in [
        ("T_plus_munu_values", T_plus),
        ("T_minus_munu_values", T_minus),
        ("tangent_vectors_values", tangents),
        ("normal_plus_values", normal_plus),
        ("normal_minus_values", normal_minus),
        ("radial_variation_tangent_weights", radial_weights),
    ]:
        if not np.all(np.isfinite(array)):
            raise ValueError(f"{name} must be finite")

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "a_grid": grid.tolist(),
        "T_plus_munu_values": T_plus.tolist(),
        "T_minus_munu_values": T_minus.tolist(),
        "tangent_vectors_values": tangents.tolist(),
        "normal_plus_values": normal_plus.tolist(),
        "normal_minus_values": normal_minus.tolist(),
        "radial_variation_tangent_weights": radial_weights.tolist(),
        "eps_Z2": float(embedding["z2_orientation_sign"]),
        "geometry_source": str(EMBEDDING_PATH),
        "stress_source": str(STRESS_PATH),
        "radial_weights_source": str(RADIAL_WEIGHTS_PATH),
        "projection_components_ready": True,
    }


def build_payload(
    *,
    embedding_path: Path = EMBEDDING_PATH,
    stress_path: Path = STRESS_PATH,
    radial_weights_path: Path = RADIAL_WEIGHTS_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "active_tunnel_embedding_geometry_inputs": embedding_path.exists(),
        "bulk_stress_on_sigma_inputs": stress_path.exists(),
        "radial_variation_tangent_weights_inputs": radial_weights_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            output = _build_output(
                load_active_z2sigma_embedding_geometry_manifest(embedding_path),
                _load_active_payload(stress_path, "bulk stress"),
                _load_active_payload(radial_weights_path, "radial weights"),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    missing = [key for key, exists in input_exists.items() if not exists]
    return {
        "status": "janus-z2-sigma-matter-flux-projection-components-from-embedding-stress-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "projection_components_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else (missing[0] if missing else "projection_component_validation"),
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_active_tunnel_embedding_geometry_inputs",
            "derive_bulk_stress_on_sigma_inputs",
            "derive_radial_variation_tangent_weights_inputs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Projection Components From Embedding/Stress Gate",
        "",
        f"Output written: `{payload['projection_components_written']}`",
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
