from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_rsigma_radial_terms import (
    load_active_z2sigma_rsigma_radial_term_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate import (
    build_payload as build_orientation_payload,
)


TERM_GRID_PATH = Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json")
GRID_INPUT_PATH = Path("outputs/active_z2_sigma/rsigma_a_grid_inputs.json")
H0_INPUT_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
RADIUS_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_inputs.json")
CURVATURE_SIGN_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_certificate_payload.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_certificate_payload_input_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_certificate_payload_input_writer_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _scalar(path: Path, key: str) -> float:
    payload = _load(path)
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{key} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{key} source must be active_derived")
    for flag in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(flag, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {flag}")
    value = float(payload["scalars"][key])
    if value <= 0.0:
        raise ValueError(f"{key} must be positive")
    return value


def _curvature_sign(path: Path) -> int:
    payload = _load(path)
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("curvature sign active_core must be Z2_tunnel_Sigma")
    value = int(payload["scalars"]["k_Z2Sigma"])
    if value not in [-1, 0, 1]:
        raise ValueError("k_Z2Sigma must be -1, 0, or 1")
    return value


def _grid_from_input(path: Path) -> list[float]:
    payload = _load(path)
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("R_Sigma grid active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("R_Sigma grid source must be active_derived")
    for flag in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(flag, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {flag}")
    grid = [float(value) for value in payload["a_grid"]]
    if len(grid) < 2 or any(value <= 0.0 for value in grid):
        raise ValueError("a_grid must contain at least two positive values")
    if any(right <= left for left, right in zip(grid, grid[1:])):
        raise ValueError("a_grid must be strictly increasing")
    return grid


def _orientation_sign() -> float:
    payload = build_orientation_payload()
    if not payload["projective_gluing_normal_orientation_sign_ready"]:
        raise ValueError("projective gluing normal orientation sign is not ready")
    if payload["formulae"]["orientation_coefficient"] != "epsilon_Z2 = -1":
        raise ValueError("unexpected Z2 orientation formula")
    return -1.0


def build_payload(
    *,
    term_grid_path: Path = TERM_GRID_PATH,
    grid_input_path: Path = GRID_INPUT_PATH,
    h0_input_path: Path = H0_INPUT_PATH,
    radius_input_path: Path = RADIUS_INPUT_PATH,
    curvature_sign_path: Path = CURVATURE_SIGN_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "rsigma_a_grid": grid_input_path.exists(),
        "term_grid_fallback": term_grid_path.exists(),
        "background_H0": h0_input_path.exists(),
        "background_curvature_radius": radius_input_path.exists(),
        "background_curvature_sign": curvature_sign_path.exists(),
    }
    output_written = False
    validation_error = None
    if (
        (input_exists["rsigma_a_grid"] or input_exists["term_grid_fallback"])
        and input_exists["background_H0"]
        and input_exists["background_curvature_radius"]
        and input_exists["background_curvature_sign"]
    ):
        try:
            if input_exists["rsigma_a_grid"]:
                a_grid = _grid_from_input(grid_input_path)
                grid_provenance = "active R_Sigma a-grid input"
            else:
                term = load_active_z2sigma_rsigma_radial_term_manifest(
                    term_grid_path,
                    expected_term_name="E_HolstNiehYan",
                )
                a_grid = term["a_grid"]
                grid_provenance = "fallback grid from active E_HolstNiehYan radial term"
            n = len(a_grid)
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "R_Sigma_solution_certificate_type": "conditional_closed_frontier_solution",
                "rsigma_payload_is_template": True,
                "rsigma_payload_not_solution_certificate": True,
                "R_Sigma_of_a_placeholder": True,
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_background_reuse_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "a_grid": a_grid,
                "a_grid_provenance": grid_provenance,
                "R_Sigma_of_a": [1.0 for _ in range(n)],
                "X_plus_of_a": [[[1.0]] for _ in range(n)],
                "X_minus_of_a": [[[-1.0]] for _ in range(n)],
                "R_curv_Z2Sigma_Mpc": _scalar(radius_input_path, "R_curv_Z2Sigma_Mpc"),
                "k_Z2Sigma": _curvature_sign(curvature_sign_path),
                "H0_Z2Sigma_km_s_Mpc": _scalar(h0_input_path, "H0_Z2Sigma_km_s_Mpc"),
                "tangent_frames_plus": [[[1.0]] for _ in range(n)],
                "tangent_frames_minus": [[[-1.0]] for _ in range(n)],
                "unit_normals_plus": [[[1.0]] for _ in range(n)],
                "unit_normals_minus": [[[-1.0]] for _ in range(n)],
                "christoffels_plus": [[[0.0]] for _ in range(n)],
                "christoffels_minus": [[[0.0]] for _ in range(n)],
                "spatial_inverse_metric": [[[1.0]] for _ in range(n)],
                "z2_orientation_sign": _orientation_sign(),
                "rsigma_solution_provenance": (
                    "active projective Z2/Sigma isotropic certificate payload"
                ),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-rsigma-certificate-payload-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "rsigma_certificate_payload_written": output_written,
        "rsigma_payload_is_template": output_written,
        "rsigma_payload_not_solution_certificate": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "rsigma_certificate_payload_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "provide_rsigma_a_grid_inputs_json_or_rsigma_E_HolstNiehYan_json_for_grid",
            "provide_background_H0_inputs_json",
            "provide_background_curvature_radius_inputs_json",
            "provide_background_curvature_sign_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Certificate Payload Input Writer Gate",
        "",
        f"Payload written: `{payload['rsigma_certificate_payload_written']}`",
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
