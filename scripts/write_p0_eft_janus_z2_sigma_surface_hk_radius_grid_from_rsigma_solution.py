from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


INPUT_PATH = Path("outputs/active_z2_sigma/rsigma_radius_solution.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_round_throat_radius_grid_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_radius_grid_from_rsigma_solution.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_radius_grid_from_rsigma_solution.json"
)


FORBIDDEN = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "archived_z4_background_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
    "fitted_counterterm_coefficient_used",
    "observational_fit_used",
]


def _load_radius(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("radius solution active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("radius solution source must be active_derived")
    for key in FORBIDDEN:
        if payload.get(key, False) is not False:
            raise ValueError(f"forbidden provenance flag must be false: {key}")
    return payload


def _build(source: dict) -> dict:
    a_grid = np.asarray(source["a_grid"], dtype=float)
    if "R_Sigma_values" in source:
        radius = np.asarray(source["R_Sigma_values"], dtype=float)
    elif "R_Sigma_of_a" in source:
        radius = np.asarray(source["R_Sigma_of_a"], dtype=float)
    else:
        raise ValueError("radius solution must provide R_Sigma_values or R_Sigma_of_a")
    if a_grid.ndim != 1 or radius.shape != a_grid.shape or a_grid.size < 1:
        raise ValueError("a_grid and R_Sigma series must be aligned one-dimensional arrays")
    if np.any(radius <= 0.0) or not np.all(np.isfinite(radius)):
        raise ValueError("R_Sigma values must be positive and finite")
    orientation = float(source.get("z2_orientation_sign", -1.0))
    if orientation not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")
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
        "observational_fit_used": False,
        "round_throat_radius_grid_ready": True,
        "a_grid": a_grid.tolist(),
        "R_Sigma_values": radius.tolist(),
        "normal_orientation_sign": orientation,
        "radius_source": "rsigma_radius_solution",
        "geometry_provenance": source.get(
            "rsigma_solution_provenance",
            "active R_Sigma solution transported to round throat h/K normal-flow grid",
        ),
    }


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
            output = _build(_load_radius(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-surface-hk-radius-grid-from-rsigma-solution",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "radius_grid_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "rsigma_radius_solution",
        "validation_error": validation_error,
        "next_required": [] if output_written else ["derive_rsigma_radius_solution_without_fit"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface h/K Radius Grid From R_Sigma Solution",
        "",
        f"Output written: `{payload['radius_grid_written']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
