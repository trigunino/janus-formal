from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.z2_sigma_extrinsic_curvature import make_z2_oriented_extrinsic_curvature_jumps


INPUT_PATH = Path("outputs/active_z2_sigma/flrw_extrinsic_curvature_grid.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_isotropic_geometry.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_surface_hk_isotropic_geometry.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_surface_hk_isotropic_geometry.json")


def _load_active_k_grid(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("K-grid active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("K-grid source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-surface-hk-isotropic-geometry",
            "active_core": "Z2_tunnel_Sigma",
            "input_manifest": str(input_path),
            "output_manifest": str(output_path),
            "surface_hk_isotropic_geometry_written": False,
            "gate_passed": False,
            "primary_blocker": "flrw_extrinsic_curvature_grid_missing",
        }

    validation_error = None
    try:
        payload = _load_active_k_grid(input_path)
        grid = payload["a_grid"]
        delta_k_s, delta_k_tau = make_z2_oriented_extrinsic_curvature_jumps(
            lambda _a: payload["K_s_plus_Z2Sigma"],
            lambda _a: payload["K_s_minus_Z2Sigma"],
            lambda _a: payload["K_tau_plus_Z2Sigma"],
            lambda _a: payload["K_tau_minus_Z2Sigma"],
            z2_orientation_sign=payload["z2_orientation_sign"],
        )
        geometry = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "compressed_planck_lcdm_used": False,
            "archived_z4_reuse_used": False,
            "observational_fit_used": False,
            "parameter_grid": grid,
            "K_s": delta_k_s(grid).tolist(),
            "K_tau": delta_k_tau(grid).tolist(),
            "sigma_orientation_plus": [1.0 for _ in grid],
            "sigma_orientation_minus": [float(payload["z2_orientation_sign"]) for _ in grid],
            "geometry_provenance": payload["K_provenance"],
            "source_K_grid": str(input_path),
        }
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(geometry, indent=2), encoding="utf-8")
        written = True
    except Exception as exc:
        validation_error = str(exc)
        written = False

    return {
        "status": "janus-z2-sigma-surface-hk-isotropic-geometry",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "surface_hk_isotropic_geometry_written": written,
        "gate_passed": written,
        "primary_blocker": "none" if written else "invalid_flrw_extrinsic_curvature_grid",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Surface h/K Isotropic Geometry",
                "",
                f"Written: `{payload['surface_hk_isotropic_geometry_written']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
