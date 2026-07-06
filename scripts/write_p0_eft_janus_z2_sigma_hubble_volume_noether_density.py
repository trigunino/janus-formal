from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_dimensionless_noether_density import (
    hubble_volume_noether_density,
)


DENSITY_PATH = Path("outputs/active_z2_sigma/dimensionless_noether_density_inputs.json")
SCALE_PATH = Path("outputs/active_z2_sigma/background_dimensionless_curvature_scale_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/hubble_volume_noether_density_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_hubble_volume_noether_density.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_hubble_volume_noether_density.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(
    *,
    density_path: Path = DENSITY_PATH,
    scale_path: Path = SCALE_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    density_exists = density_path.exists()
    scale_exists = scale_path.exists()
    output_written = False
    validation_error = None
    output = None
    if density_exists and scale_exists:
        try:
            density = _load(density_path)
            scale = _load(scale_path)
            if density.get("active_core") != "Z2_tunnel_Sigma":
                raise ValueError("density active_core must be Z2_tunnel_Sigma")
            if scale.get("active_core") != "Z2_tunnel_Sigma":
                raise ValueError("scale active_core must be Z2_tunnel_Sigma")
            derived = hubble_volume_noether_density(
                density["dimensionless_density"][
                    "baryon_number_density0_times_Rcurv3_Z2Sigma"
                ],
                scale["scalars"]["h0_R_curv_over_c_Z2Sigma"],
            )
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_rd_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "dimensionless_density": derived,
                "remaining_dimensional_blocker": "H0_Z2Sigma_or_R_curv_Z2Sigma_m_for_SI_density",
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-hubble-volume-noether-density",
        "active_core": "Z2_tunnel_Sigma",
        "density_manifest": str(density_path),
        "scale_manifest": str(scale_path),
        "output_manifest": str(output_path),
        "density_manifest_exists": density_exists,
        "scale_manifest_exists": scale_exists,
        "hubble_volume_density_written": output_written,
        "output": output,
        "full_no_fit_prediction_ready": False,
        "gate_passed": output_written,
        "primary_blocker": "none"
        if output_written
        else "dimensionless_noether_density_or_H0Rcurv_over_c",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Hubble-Volume Noether Density",
                "",
                f"Density manifest exists: `{payload['density_manifest_exists']}`",
                f"Scale manifest exists: `{payload['scale_manifest_exists']}`",
                f"Hubble-volume density written: `{payload['hubble_volume_density_written']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
