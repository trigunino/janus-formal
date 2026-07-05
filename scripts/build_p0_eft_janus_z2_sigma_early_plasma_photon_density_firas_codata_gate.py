from __future__ import annotations

import json
from pathlib import Path


CONSTANTS_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
TEMPERATURE_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_density_firas_codata_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_photon_density_firas_codata_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_photon_density_firas_codata_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _compute(constants: dict, temperature: dict) -> dict:
    a_rad = float(constants["constants"]["radiation_constant_J_m3_K4"])
    t0 = float(temperature["normalizations"]["photon_temperature0_Z2Sigma"])
    if a_rad <= 0.0 or t0 <= 0.0:
        raise ValueError("radiation constant and photon temperature must be positive")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "direct_noncompressed_observation_plus_codata",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_fit_used": False,
        "normalizations": {
            "rho_photon0_Z2Sigma_J_m3": a_rad * t0**4,
        },
        "normalization_provenance": {
            "rho_photon0_Z2Sigma": (
                "rho_gamma0=a_rad*T_gamma0^4 from CODATA radiation constant "
                "and COBE_FIRAS direct monopole temperature"
            ),
        },
        "input_manifests": {
            "codata_constants": str(CONSTANTS_PATH),
            "photon_temperature_firas": str(TEMPERATURE_PATH),
        },
    }


def build_payload(
    *,
    constants_path: Path = CONSTANTS_PATH,
    temperature_path: Path = TEMPERATURE_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = True,
) -> dict:
    constants_exists = constants_path.exists()
    temperature_exists = temperature_path.exists()
    output_written = False
    output_valid = False
    validation_error = None
    if constants_exists and temperature_exists and write_output:
        try:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(
                json.dumps(_compute(_load(constants_path), _load(temperature_path)), indent=2),
                encoding="utf-8",
            )
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    if output_path.exists():
        try:
            payload = _load(output_path)
            output_valid = (
                payload.get("active_core") == "Z2_tunnel_Sigma"
                and payload.get("source") == "direct_noncompressed_observation_plus_codata"
                and payload.get("compressed_planck_lcdm_rd_used") is False
                and payload.get("archived_z4_reuse_used") is False
                and payload.get("phenomenological_holst_bao_scan_used") is False
                and float(payload["normalizations"]["rho_photon0_Z2Sigma_J_m3"]) > 0.0
            )
        except Exception as exc:
            validation_error = str(exc)
    rho_value = None
    if output_valid:
        rho_value = float(_load(output_path)["normalizations"]["rho_photon0_Z2Sigma_J_m3"])
    return {
        "status": "janus-z2-sigma-early-plasma-photon-density-firas-codata-gate",
        "active_core": "Z2_tunnel_Sigma",
        "constants_manifest_exists": constants_exists,
        "temperature_manifest_exists": temperature_exists,
        "output_manifest": str(output_path),
        "rho_photon0_Z2Sigma_J_m3": rho_value,
        "output_written": output_written,
        "output_exists": output_path.exists(),
        "output_valid": output_valid,
        "validation_error": validation_error,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "uses_observational_fit": False,
        "gate_passed": output_valid,
        "does_not_fix_baryon_or_ionization_normalizations": True,
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
                "# Janus Z2/Sigma Early-Plasma Photon Density FIRAS+CODATA Gate",
                "",
                f"rho_photon0: `{payload['rho_photon0_Z2Sigma_J_m3']}` J/m^3",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
