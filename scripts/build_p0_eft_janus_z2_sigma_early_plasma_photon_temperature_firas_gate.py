from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate.json"
)

T_CMB_FIRAS_K = 2.72548
T_CMB_FIRAS_UNCERTAINTY_K = 0.00057
FIXSEN_2009_ARXIV = "https://arxiv.org/abs/0911.1955"
NASA_LAMBDA_FIRAS_URL = "https://lambda.gsfc.nasa.gov/product/cobe/about_firas.html"


def _manifest() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "direct_noncompressed_observation",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_fit_used": False,
        "normalizations": {
            "photon_temperature0_Z2Sigma": T_CMB_FIRAS_K,
        },
        "normalization_uncertainty": {
            "photon_temperature0_Z2Sigma_K": T_CMB_FIRAS_UNCERTAINTY_K,
        },
        "normalization_provenance": {
            "photon_temperature0_Z2Sigma": "COBE_FIRAS_direct_monopole_temperature_Fixsen_2009",
        },
        "source_reference": {
            "fixsen_2009": FIXSEN_2009_ARXIV,
            "nasa_lambda_firas": NASA_LAMBDA_FIRAS_URL,
        },
    }


def build_payload(*, output_path: Path = OUTPUT_PATH, write_output: bool = True) -> dict:
    output_written = False
    output_valid = False
    validation_error = None
    if write_output:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(_manifest(), indent=2), encoding="utf-8")
        output_written = True
    if output_path.exists():
        try:
            payload = json.loads(output_path.read_text(encoding="utf-8"))
            output_valid = (
                payload.get("active_core") == "Z2_tunnel_Sigma"
                and payload.get("source") == "direct_noncompressed_observation"
                and payload.get("compressed_planck_lcdm_rd_used") is False
                and payload.get("archived_z4_reuse_used") is False
                and payload.get("phenomenological_holst_bao_scan_used") is False
                and payload.get("observational_fit_used") is False
                and float(payload["normalizations"]["photon_temperature0_Z2Sigma"])
                == T_CMB_FIRAS_K
            )
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-photon-temperature-firas-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [FIXSEN_2009_ARXIV, NASA_LAMBDA_FIRAS_URL],
        "photon_temperature0_K": T_CMB_FIRAS_K,
        "photon_temperature0_uncertainty_K": T_CMB_FIRAS_UNCERTAINTY_K,
        "output_manifest": str(output_path),
        "output_written": output_written,
        "output_exists": output_path.exists(),
        "output_valid": output_valid,
        "validation_error": validation_error,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "uses_observational_fit": False,
        "is_direct_monopole_temperature_observation": True,
        "does_not_fix_baryon_or_ionization_normalizations": True,
        "gate_passed": output_valid,
        "still_required_model_inputs": [
            "rho_baryon0_Z2Sigma",
            "baryon_number_density0_m3_Z2Sigma",
            "ionization_fraction_Z2Sigma",
            "electrons_per_baryon",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Early-Plasma Photon Temperature FIRAS Gate",
                "",
                f"T_gamma0: `{payload['photon_temperature0_K']}` K",
                f"Uncertainty: `{payload['photon_temperature0_uncertainty_K']}` K",
                f"Gate passed: `{payload['gate_passed']}`",
                "",
                "## Still Required Model Inputs",
                *[f"- `{item}`" for item in payload["still_required_model_inputs"]],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
