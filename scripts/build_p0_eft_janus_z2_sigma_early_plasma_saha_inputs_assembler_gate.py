from __future__ import annotations

import json
import tempfile
from pathlib import Path

from janus_lab.z2_sigma_early_plasma_inputs import load_active_z2sigma_early_plasma_input_manifest


CONSTANTS_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
TEMPERATURE_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json")
SAHA_HISTORY_PATH = Path("outputs/active_z2_sigma/early_plasma_saha_ionization_history_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_saha_inputs_assembler_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_saha_inputs_assembler_gate.json")


FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_rd_used",
    "archived_z4_reuse_used",
    "phenomenological_holst_bao_scan_used",
]


def _load(path: Path) -> dict | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def _valid(payload: dict | None, source: str) -> bool:
    if payload is None:
        return False
    return (
        payload.get("active_core") == "Z2_tunnel_Sigma"
        and payload.get("source") == source
        and all(payload.get(key) is False for key in FORBIDDEN_FLAGS)
    )


def _assemble(constants: dict, temperature: dict, saha: dict) -> dict:
    constants_values = constants["constants"]
    constants_provenance = constants["constant_provenance"]
    temperature_values = temperature["normalizations"]
    temperature_provenance = temperature["normalization_provenance"]
    saha_inputs = saha["normalization_inputs"]
    saha_provenance = saha["normalization_provenance"]
    n_b0 = float(saha_inputs["baryon_number_density0_m3_Z2Sigma"])
    baryon_mass = float(constants_values["baryon_mass_kg"])
    candidate = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": saha["z_grid"],
        "normalizations": {
            "rho_baryon0_Z2Sigma": n_b0 * baryon_mass,
            "photon_temperature0_Z2Sigma": float(
                temperature_values["photon_temperature0_Z2Sigma"]
            ),
            "radiation_constant_J_m3_K4": float(
                constants_values["radiation_constant_J_m3_K4"]
            ),
            "baryon_mass_kg": baryon_mass,
            "baryon_number_density0_m3_Z2Sigma": n_b0,
            "electrons_per_baryon": float(saha["electrons_per_baryon"]),
            "sigma_thomson_m2": float(constants_values["sigma_thomson_m2"]),
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
            "baryon_number_density0_m3_Z2Sigma": saha_provenance[
                "baryon_number_density0_m3_Z2Sigma"
            ],
            "electrons_per_baryon": saha_provenance["electrons_per_baryon"],
            "sigma_thomson_m2": constants_provenance["sigma_thomson_m2"],
        },
        "ionization_history": {
            "z_grid": saha["z_grid"],
            "ionization_fraction_Z2Sigma": saha["ionization_fraction_Z2Sigma"],
            "provenance": "active_saha_ionization_history_gate",
        },
    }
    load_active_z2sigma_early_plasma_input_manifest_from_payload(candidate)
    return candidate


def load_active_z2sigma_early_plasma_input_manifest_from_payload(payload: dict) -> dict:
    handle = tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".json", delete=False)
    temp_path = Path(handle.name)
    try:
        json.dump(payload, handle)
        handle.close()
        return load_active_z2sigma_early_plasma_input_manifest(temp_path)
    finally:
        handle.close()
        temp_path.unlink(missing_ok=True)


def build_payload(
    *,
    constants_path: Path = CONSTANTS_PATH,
    temperature_path: Path = TEMPERATURE_PATH,
    saha_history_path: Path = SAHA_HISTORY_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = True,
) -> dict:
    constants = _load(constants_path)
    temperature = _load(temperature_path)
    saha = _load(saha_history_path)
    constants_valid = _valid(constants, "active_derived")
    temperature_valid = _valid(temperature, "direct_noncompressed_observation")
    saha_valid = _valid(saha, "active_derived")
    can_assemble = False
    output_written = False
    validation_error = None
    if constants_valid and temperature_valid and saha_valid:
        try:
            manifest = _assemble(constants, temperature, saha)
            can_assemble = True
            if write_output:
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
                output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-saha-inputs-assembler-gate",
        "active_core": "Z2_tunnel_Sigma",
        "constants_valid": constants_valid,
        "temperature_valid": temperature_valid,
        "saha_history_valid": saha_valid,
        "early_plasma_inputs_ready": can_assemble,
        "early_plasma_inputs_written": output_written,
        "output_manifest": str(output_path),
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": can_assemble,
        "validation_error": validation_error,
        "next_required": [
            "run_early_plasma_manifest_writer_from_inputs_gate",
            "run_thomson_drag_rate_builder_gate",
            "solve_z_d_from_active_H_Z2Sigma_and_Gamma_drag_Z2Sigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Early-Plasma Saha Inputs Assembler Gate",
                "",
                f"Constants valid: `{payload['constants_valid']}`",
                f"Temperature valid: `{payload['temperature_valid']}`",
                f"Saha history valid: `{payload['saha_history_valid']}`",
                f"Inputs ready: `{payload['early_plasma_inputs_ready']}`",
                f"Inputs written: `{payload['early_plasma_inputs_written']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
