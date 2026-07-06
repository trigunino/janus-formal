from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_density_normalization import (
    baryon_density_from_hubble_volume_invariant,
    baryon_density_from_r3_invariant,
)


R3_DENSITY_PATH = Path("outputs/active_z2_sigma/dimensionless_noether_density_inputs.json")
HUBBLE_DENSITY_PATH = Path("outputs/active_z2_sigma/hubble_volume_noether_density_inputs.json")
R_CURV_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_inputs.json")
H0_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_baryon_number_density_noether_volume_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_baryon_density_si_from_dimensionless_invariants.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_baryon_density_si_from_dimensionless_invariants.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _check_active(payload: dict, label: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")


def _provenance(payload: dict, key: str) -> str:
    text = str(payload.get("scalar_provenance", {}).get(key, "")).strip()
    if not text:
        text = str(payload.get("normalization_provenance", {}).get(key, "")).strip()
    if not text:
        raise ValueError(f"Missing provenance for {key}")
    lowered = text.lower()
    for token in ["planck", "lcdm", "z4", "fit", "bao_scan"]:
        if token in lowered:
            raise ValueError(f"Forbidden provenance for {key}: {text}")
    return text


def _from_r_curv(r3_density_path: Path, r_curv_path: Path) -> tuple[float, str] | None:
    if not (r3_density_path.exists() and r_curv_path.exists()):
        return None
    density = _load(r3_density_path)
    radius = _load(r_curv_path)
    _check_active(density, "density")
    _check_active(radius, "radius")
    value = density["dimensionless_density"]["baryon_number_density0_times_Rcurv3_Z2Sigma"]
    r_mpc = float(radius["scalars"]["R_curv_Z2Sigma_Mpc"])
    r_m = r_mpc * 3.0856775814913673e22
    prov = _provenance(radius, "R_curv_Z2Sigma")
    return baryon_density_from_r3_invariant(value, r_m), f"R_curv_route:({prov})"


def _from_h0(hubble_density_path: Path, h0_path: Path) -> tuple[float, str] | None:
    if not (hubble_density_path.exists() and h0_path.exists()):
        return None
    density = _load(hubble_density_path)
    h0 = _load(h0_path)
    _check_active(density, "hubble density")
    _check_active(h0, "H0")
    value = density["dimensionless_density"][
        "baryon_number_density0_times_Hubble_volume_Z2Sigma"
    ]
    h0_value = float(h0["scalars"]["H0_Z2Sigma_km_s_Mpc"])
    prov = _provenance(h0, "H0_Z2Sigma")
    return baryon_density_from_hubble_volume_invariant(value, h0_value), f"H0_route:({prov})"


def build_payload(
    *,
    r3_density_path: Path = R3_DENSITY_PATH,
    hubble_density_path: Path = HUBBLE_DENSITY_PATH,
    r_curv_path: Path = R_CURV_PATH,
    h0_path: Path = H0_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    output_written = False
    validation_error = None
    route = None
    density_value = None
    try:
        r_route = _from_r_curv(r3_density_path, r_curv_path)
        h_route = _from_h0(hubble_density_path, h0_path)
        if r_route and h_route:
            if abs(r_route[0] - h_route[0]) > max(abs(r_route[0]), abs(h_route[0])) * 1.0e-8:
                raise ValueError("R_curv and H0 density routes disagree")
            density_value, route = r_route[0], "R_curv_and_H0_consistent"
            provenance = f"{r_route[1]};{h_route[1]}"
        elif r_route:
            density_value, provenance = r_route
            route = "R_curv"
        elif h_route:
            density_value, provenance = h_route
            route = "H0"
        else:
            provenance = None
        if density_value is not None:
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_rd_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "normalizations": {
                    "baryon_number_density0_m3_Z2Sigma": density_value,
                },
                "normalization_provenance": {
                    "baryon_number_density0_m3_Z2Sigma": provenance,
                },
                "normalization_route": route,
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
    except Exception as exc:
        validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-baryon-density-si-from-dimensionless-invariants",
        "active_core": "Z2_tunnel_Sigma",
        "route": route,
        "density_written": output_written,
        "baryon_number_density0_m3_Z2Sigma": density_value,
        "output_manifest": str(output_path),
        "full_no_fit_prediction_ready": False,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "H0_Z2Sigma_or_R_curv_Z2Sigma_m",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma SI Baryon Density From Dimensionless Invariants",
                "",
                f"Route: `{payload['route']}`",
                f"Density written: `{payload['density_written']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
