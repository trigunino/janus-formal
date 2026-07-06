from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_dimensionless_noether_density import (
    dimensionless_noether_density_r3,
)
from src.janus_lab.z2_sigma_projected_baryon_charge import (
    load_active_projected_baryon_charge_manifest,
)


CHARGE_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/dimensionless_noether_density_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dimensionless_noether_density_from_charge.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dimensionless_noether_density_from_charge.json"
)


def build_payload(
    *,
    charge_path: Path = CHARGE_PATH,
    output_path: Path = OUTPUT_PATH,
    quotient_spatial_slice: str = "RP3",
) -> dict:
    charge_exists = charge_path.exists()
    output_written = False
    validation_error = None
    density = None
    if charge_exists:
        try:
            charge = load_active_projected_baryon_charge_manifest(charge_path)
            charge_value = charge["normalizations"]["projected_baryon_number_charge_Z2Sigma"]
            density = dimensionless_noether_density_r3(
                charge_value,
                quotient_spatial_slice=quotient_spatial_slice,
            )
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_rd_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_baryon_fit_used": False,
                "dimensionless_density": density,
                "normalization_provenance": {
                    "baryon_number_density0_times_Rcurv3_Z2Sigma": (
                        "derived_from_projected_Noether_charge_and_projective_spatial_volume_factor"
                    )
                },
                "remaining_dimensional_blocker": "R_curv_Z2Sigma_m",
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-dimensionless-noether-density-from-charge",
        "active_core": "Z2_tunnel_Sigma",
        "charge_manifest": str(charge_path),
        "output_manifest": str(output_path),
        "charge_manifest_exists": charge_exists,
        "dimensionless_density_written": output_written,
        "density_payload": density,
        "remaining_dimensional_blocker": "R_curv_Z2Sigma_m",
        "full_no_fit_prediction_ready": False,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "projected_baryon_noether_charge_inputs_json",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Dimensionless Noether Density",
                "",
                f"Charge manifest exists: `{payload['charge_manifest_exists']}`",
                f"Dimensionless density written: `{payload['dimensionless_density_written']}`",
                f"Remaining dimensional blocker: `{payload['remaining_dimensional_blocker']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
