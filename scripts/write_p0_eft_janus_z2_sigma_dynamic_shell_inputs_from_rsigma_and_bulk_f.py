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


CERTIFICATE_PATH = Path("outputs/active_z2_sigma/rsigma_solution_certificate.json")
KINEMATICS_PATH = Path("outputs/active_z2_sigma/dynamic_shell_radius_kinematics_inputs.json")
BULK_F_PATH = Path("outputs/active_z2_sigma/static_areal_bulk_f_pm_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/dynamic_shell_extrinsic_curvature_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dynamic_shell_inputs_from_rsigma_and_bulk_f.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dynamic_shell_inputs_from_rsigma_and_bulk_f.json"
)


def _load_radius_payload(path: Path) -> dict:
    try:
        cert = load_active_z2sigma_rsigma_solution_certificate(path)
        return {
            "a_grid": cert["a_grid"],
            "R_Sigma_of_a": cert["R_Sigma_of_a"],
            "z2_orientation_sign": cert["z2_orientation_sign"],
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
            "z2_orientation_sign": payload["z2_orientation_sign"],
            "provenance": payload["rsigma_solution_provenance"],
        }


def _load_active(path: Path, label: str) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{label} source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def _series(payload: dict, key: str, shape: tuple[int, ...]) -> list[float]:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite and aligned with a_grid")
    return values.tolist()


def build_payload(
    *,
    certificate_path: Path = CERTIFICATE_PATH,
    kinematics_path: Path = KINEMATICS_PATH,
    bulk_f_path: Path = BULK_F_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    exists = {
        "rsigma_solution_certificate": certificate_path.exists(),
        "dynamic_shell_radius_kinematics": kinematics_path.exists(),
        "static_areal_bulk_f_pm": bulk_f_path.exists(),
    }
    if not all(exists.values()):
        return {
            "status": "janus-z2-sigma-dynamic-shell-inputs-from-rsigma-and-bulk-f",
            "active_core": "Z2_tunnel_Sigma",
            "input_exists": exists,
            "output_manifest": str(output_path),
            "dynamic_shell_inputs_written": False,
            "gate_passed": False,
            "primary_blocker": "dynamic_shell_rsigma_kinematics_or_bulk_f_inputs_missing",
        }

    validation_error = None
    try:
        radius = _load_radius_payload(certificate_path)
        kin = _load_active(kinematics_path, "radius kinematics")
        bulk = _load_active(bulk_f_path, "bulk f_pm")
        grid = np.asarray(radius["a_grid"], dtype=float)
        if grid.ndim != 1 or len(grid) < 2:
            raise ValueError("certificate a_grid must contain at least two points")
        shape = grid.shape
        if list(kin.get("a_grid", [])) != radius["a_grid"]:
            raise ValueError("radius kinematics a_grid must match R_Sigma payload")
        if list(bulk.get("a_grid", [])) != radius["a_grid"]:
            raise ValueError("bulk f_pm a_grid must match R_Sigma payload")
        manifest = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
            "phenomenological_holst_bao_scan_used": False,
            "observational_fit_used": False,
            "a_grid": radius["a_grid"],
            "R_Sigma_of_a": _series(radius, "R_Sigma_of_a", shape),
            "R_dot_of_a": _series(kin, "R_dot_of_a", shape),
            "R_ddot_of_a": _series(kin, "R_ddot_of_a", shape),
            "f_plus_of_R": _series(bulk, "f_plus_of_R", shape),
            "f_minus_of_R": _series(bulk, "f_minus_of_R", shape),
            "df_plus_dR": _series(bulk, "df_plus_dR", shape),
            "df_minus_dR": _series(bulk, "df_minus_dR", shape),
            "epsilon_plus": float(bulk["epsilon_plus"]),
            "epsilon_minus": float(bulk["epsilon_minus"]),
            "z2_orientation_sign": float(radius["z2_orientation_sign"]),
            "dynamic_shell_provenance": (
                f"R_Sigma=({radius['provenance']}); "
                f"kinematics=({kin['kinematics_provenance']}); "
                f"bulk_f=({bulk['bulk_f_provenance']})"
            ),
        }
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
        written = True
    except Exception as exc:
        validation_error = str(exc)
        written = False

    return {
        "status": "janus-z2-sigma-dynamic-shell-inputs-from-rsigma-and-bulk-f",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": exists,
        "output_manifest": str(output_path),
        "dynamic_shell_inputs_written": written,
        "gate_passed": written,
        "primary_blocker": "none" if written else "invalid_dynamic_shell_source_inputs",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Dynamic Shell Inputs From R_Sigma And Bulk f",
                "",
                f"Written: `{payload['dynamic_shell_inputs_written']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
