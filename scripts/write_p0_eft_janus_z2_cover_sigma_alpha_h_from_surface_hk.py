from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_surface_hk import polynomial_surface_hk_isotropic_alpha_components


COEFF_PATH = Path("outputs/active_z2_sigma/surface_hk_active_density_coefficients.json")
GEOM_PATH = Path("outputs/active_z2_sigma/surface_hk_isotropic_geometry.json")
OUTPUT_PATH = Path("outputs/active_z2_cover/sigma_alpha_h_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_sigma_alpha_h_from_surface_hk.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_sigma_alpha_h_from_surface_hk.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _ready(payload: dict, *, source: str) -> bool:
    return payload.get("active_core") == "Z2_tunnel_Sigma" and payload.get("source") == source


def _coefficient(payload: dict, key: str):
    return payload[key] if key in payload else payload[f"{key}_values"]


def build_payload(
    coeff_path: Path = COEFF_PATH,
    geom_path: Path = GEOM_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    missing = [str(path) for path in [coeff_path, geom_path] if not path.exists()]
    if missing:
        return {
            "status": "janus-z2-cover-sigma-alpha-h-from-surface-hk",
            "active_core": "JanusZ2CoverMasterAction",
            "missing_inputs": missing,
            "sigma_alpha_h_inputs_written": False,
            "gate_passed": False,
            "primary_blocker": "surface_hk_coefficients_or_geometry_missing",
        }
    coeff = _load(coeff_path)
    geom = _load(geom_path)
    if not _ready(coeff, source="active_derived"):
        raise ValueError("coefficient payload must be active Z2_tunnel_Sigma / active_derived")
    if not _ready(geom, source="active_derived"):
        raise ValueError("geometry payload must be active Z2_tunnel_Sigma / active_derived")
    for flag in [
        "compressed_planck_lcdm_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "observational_fit_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if coeff.get(flag, False) is not False or geom.get(flag, False) is not False:
            raise ValueError(f"{flag} must be false")

    alpha = polynomial_surface_hk_isotropic_alpha_components(
        a0=_coefficient(coeff, "a0"),
        a1=_coefficient(coeff, "a1"),
        a2=_coefficient(coeff, "a2"),
        a3=_coefficient(coeff, "a3"),
        K_tau=geom["K_tau"],
        K_s=geom["K_s"],
    )
    manifest = {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "master_boundary_variation_alpha_h",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "two_independent_actions_used": False,
        "full_no_fit_prediction_ready": False,
        "parameter_grid": geom["parameter_grid"],
        "alpha_h_tau": alpha["alpha_h_tau"].tolist(),
        "alpha_h_s": alpha["alpha_h_s"].tolist(),
        "sigma_orientation_plus": geom["sigma_orientation_plus"],
        "sigma_orientation_minus": geom["sigma_orientation_minus"],
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-cover-sigma-alpha-h-from-surface-hk",
        "active_core": "JanusZ2CoverMasterAction",
        "sigma_alpha_h_inputs_written": True,
        "output_path": str(output_path),
        "gate_passed": True,
        "primary_blocker": "none",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Cover Sigma Alpha_h From Surface h/K",
                "",
                f"Written: `{payload['sigma_alpha_h_inputs_written']}`",
                f"Primary blocker: `{payload.get('primary_blocker', 'none')}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
