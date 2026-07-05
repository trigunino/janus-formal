from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_early_plasma_inputs import (
    build_active_z2sigma_baryon_photon_input_payload,
    build_active_z2sigma_ionization_thomson_input_payload,
)


CONSTANTS_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
TEMPERATURE_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json")
MODEL_INPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_model_normalization_inputs.json")
BARYON_PHOTON_OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_baryon_photon_normalization_inputs.json"
)
IONIZATION_THOMSON_OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_ionization_thomson_normalization_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_model_normalization_assembler_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_model_normalization_assembler_gate.json"
)

MODEL_FIELDS = [
    "baryon_number_density0_m3_Z2Sigma",
    "ionization_fraction_Z2Sigma",
    "electrons_per_baryon",
]


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _validate_common(payload: dict) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Model payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Model payload source must be active_derived")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _assemble(constants: dict, temperature: dict, model: dict) -> tuple[dict, dict]:
    _validate_common(model)
    if constants.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Constants payload active_core must be Z2_tunnel_Sigma")
    if constants.get("source") != "active_derived":
        raise ValueError("Constants payload source must be active_derived")
    if temperature.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Temperature payload active_core must be Z2_tunnel_Sigma")
    if temperature.get("source") != "direct_noncompressed_observation":
        raise ValueError("Temperature payload source must be direct_noncompressed_observation")

    normalizations = model.get("normalizations", {})
    provenance = model.get("normalization_provenance", {})
    for field in MODEL_FIELDS:
        if field not in normalizations:
            raise ValueError(f"Missing model normalization: {field}")
        if field not in provenance:
            raise ValueError(f"Missing model normalization provenance: {field}")

    constants_payload = constants["constants"]
    constants_provenance = constants["constant_provenance"]
    temperature_payload = temperature["normalizations"]
    temperature_provenance = temperature["normalization_provenance"]
    base = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": model["z_grid"],
    }
    baryon_photon = {
        **base,
        "normalizations": {
            "rho_baryon0_Z2Sigma": (
                float(normalizations["baryon_number_density0_m3_Z2Sigma"])
                * float(constants_payload["baryon_mass_kg"])
            ),
            "photon_temperature0_Z2Sigma": temperature_payload[
                "photon_temperature0_Z2Sigma"
            ],
            "radiation_constant_J_m3_K4": constants_payload["radiation_constant_J_m3_K4"],
            "baryon_mass_kg": constants_payload["baryon_mass_kg"],
            "baryon_number_density0_m3_Z2Sigma": normalizations[
                "baryon_number_density0_m3_Z2Sigma"
            ],
        },
        "normalization_provenance": {
            "rho_baryon0_Z2Sigma": (
                "derived_from_active_baryon_number_density_and_CODATA_baryon_mass"
            ),
            "photon_temperature0_Z2Sigma": temperature_provenance[
                "photon_temperature0_Z2Sigma"
            ],
            "radiation_constant_J_m3_K4": constants_provenance[
                "radiation_constant_J_m3_K4"
            ],
            "baryon_mass_kg": constants_provenance["baryon_mass_kg"],
            "baryon_number_density0_m3_Z2Sigma": provenance[
                "baryon_number_density0_m3_Z2Sigma"
            ],
        },
    }
    ionization_thomson = {
        **base,
        "normalizations": {
            "ionization_fraction_Z2Sigma": normalizations["ionization_fraction_Z2Sigma"],
            "electrons_per_baryon": normalizations["electrons_per_baryon"],
            "sigma_thomson_m2": constants_payload["sigma_thomson_m2"],
        },
        "normalization_provenance": {
            "ionization_fraction_Z2Sigma": provenance["ionization_fraction_Z2Sigma"],
            "electrons_per_baryon": provenance["electrons_per_baryon"],
            "sigma_thomson_m2": constants_provenance["sigma_thomson_m2"],
        },
    }
    return (
        build_active_z2sigma_baryon_photon_input_payload(baryon_photon),
        build_active_z2sigma_ionization_thomson_input_payload(ionization_thomson),
    )


def build_payload(
    *,
    constants_path: Path = CONSTANTS_PATH,
    temperature_path: Path = TEMPERATURE_PATH,
    model_input_path: Path = MODEL_INPUT_PATH,
    baryon_photon_output_path: Path = BARYON_PHOTON_OUTPUT_PATH,
    ionization_thomson_output_path: Path = IONIZATION_THOMSON_OUTPUT_PATH,
) -> dict:
    constants_exists = constants_path.exists()
    temperature_exists = temperature_path.exists()
    model_input_exists = model_input_path.exists()
    output_written = False
    validation_error = None
    if constants_exists and temperature_exists and model_input_exists:
        try:
            baryon_photon, ionization_thomson = _assemble(
                _load(constants_path),
                _load(temperature_path),
                _load(model_input_path),
            )
            baryon_photon_output_path.parent.mkdir(parents=True, exist_ok=True)
            ionization_thomson_output_path.parent.mkdir(parents=True, exist_ok=True)
            baryon_photon_output_path.write_text(
                json.dumps(baryon_photon, indent=2),
                encoding="utf-8",
            )
            ionization_thomson_output_path.write_text(
                json.dumps(ionization_thomson, indent=2),
                encoding="utf-8",
            )
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-model-normalization-assembler-gate",
        "active_core": "Z2_tunnel_Sigma",
        "constants_manifest": str(constants_path),
        "temperature_manifest": str(temperature_path),
        "model_input_manifest": str(model_input_path),
        "baryon_photon_output_manifest": str(baryon_photon_output_path),
        "ionization_thomson_output_manifest": str(ionization_thomson_output_path),
        "constants_manifest_exists": constants_exists,
        "temperature_manifest_exists": temperature_exists,
        "model_input_manifest_exists": model_input_exists,
        "split_normalization_inputs_written": output_written,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_written,
        "primary_blocker": (
            "none" if output_written else "active_early_plasma_model_normalizations"
        ),
        "validation_error": validation_error,
        "next_required": [
            "derive_active_early_plasma_model_normalizations",
            "run_early_plasma_photon_temperature_firas_gate",
            "run_early_plasma_input_writers_and_assembler",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early-Plasma Model Normalization Assembler Gate",
        "",
        f"CODATA constants manifest exists: `{payload['constants_manifest_exists']}`",
        f"FIRAS temperature manifest exists: `{payload['temperature_manifest_exists']}`",
        f"Model input manifest exists: `{payload['model_input_manifest_exists']}`",
        f"Split normalization inputs written: `{payload['split_normalization_inputs_written']}`",
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
