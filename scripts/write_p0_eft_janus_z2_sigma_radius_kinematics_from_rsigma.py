from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.z2_sigma_rsigma_certificate import load_active_z2sigma_rsigma_solution_certificate


INPUT_PATH = Path("outputs/active_z2_sigma/rsigma_solution_certificate.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/dynamic_shell_radius_kinematics_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_radius_kinematics_from_rsigma.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_radius_kinematics_from_rsigma.json")


def _load_radius_payload(path: Path) -> dict:
    try:
        cert = load_active_z2sigma_rsigma_solution_certificate(path)
        return {
            "a_grid": cert["a_grid"],
            "R_Sigma_of_a": cert["R_Sigma_of_a"],
            "provenance": cert["rsigma_solution_provenance"],
        }
    except Exception:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if payload.get("active_core") != "Z2_tunnel_Sigma":
            raise ValueError("R_Sigma radius payload active_core must be Z2_tunnel_Sigma")
        if payload.get("source") != "active_derived":
            raise ValueError("R_Sigma radius payload source must be active_derived")
        for key in [
            "compressed_planck_lcdm_background_used",
            "archived_z4_reuse_used",
            "phenomenological_holst_bao_scan_used",
            "observational_fit_used",
        ]:
            if payload.get(key) is not False:
                raise ValueError(f"Forbidden provenance flag must be false: {key}")
        return {
            "a_grid": payload["a_grid"],
            "R_Sigma_of_a": payload["R_Sigma_of_a"],
            "provenance": payload["rsigma_solution_provenance"],
        }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-radius-kinematics-from-rsigma",
            "active_core": "Z2_tunnel_Sigma",
            "input_manifest": str(input_path),
            "output_manifest": str(output_path),
            "radius_kinematics_written": False,
            "gate_passed": False,
            "primary_blocker": "rsigma_solution_certificate_missing",
        }
    validation_error = None
    try:
        radius_payload = _load_radius_payload(input_path)
        grid = np.asarray(radius_payload["a_grid"], dtype=float)
        radius = np.asarray(radius_payload["R_Sigma_of_a"], dtype=float)
        if grid.ndim != 1 or len(grid) < 3:
            raise ValueError("a_grid must have at least three points for second derivatives")
        if np.any(np.diff(grid) <= 0.0):
            raise ValueError("a_grid must be strictly increasing")
        r_dot = np.gradient(radius, grid, edge_order=2)
        r_ddot = np.gradient(r_dot, grid, edge_order=2)
        manifest = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
            "phenomenological_holst_bao_scan_used": False,
            "observational_fit_used": False,
            "a_grid": grid.tolist(),
            "R_dot_of_a": r_dot.tolist(),
            "R_ddot_of_a": r_ddot.tolist(),
            "kinematics_provenance": (
                "finite_difference_on_active_RSigma_solution_certificate:"
                f"({radius_payload['provenance']})"
            ),
            "finite_difference_variable": "a_grid",
            "proper_time_identification_assumed": "a_grid_parameterized_chain; replace with tau-grid if derived",
        }
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
        written = True
    except Exception as exc:
        validation_error = str(exc)
        written = False
    return {
        "status": "janus-z2-sigma-radius-kinematics-from-rsigma",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "radius_kinematics_written": written,
        "gate_passed": written,
        "primary_blocker": "none" if written else "invalid_rsigma_solution_certificate_for_kinematics",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Radius Kinematics From R_Sigma",
                "",
                f"Written: `{payload['radius_kinematics_written']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
