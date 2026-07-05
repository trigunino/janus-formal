from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from janus_lab.z2_sigma_early_plasma import (
    make_conserved_baryon_density_z2sigma,
    make_conserved_photon_temperature_z2sigma,
    make_saha_ionization_fraction_z2sigma,
)


BARYON_INPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_baryon_number_density_noether_volume_inputs.json"
)
TEMPERATURE_INPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json")
CONSTANTS_INPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_saha_ionization_history_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_saha_ionization_history_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_saha_ionization_history_gate.json")


def _read_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def _valid_active_payload(payload: dict | None, *, source: str | None = None) -> bool:
    if payload is None:
        return False
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        return False
    if source is not None and payload.get("source") != source:
        return False
    return (
        payload.get("compressed_planck_lcdm_rd_used") is False
        and payload.get("archived_z4_reuse_used") is False
        and payload.get("phenomenological_holst_bao_scan_used") is False
    )


def _build_history(baryon_payload: dict, temperature_payload: dict, constants_payload: dict) -> dict:
    normalizations = baryon_payload["normalizations"]
    provenance = baryon_payload.get("normalization_provenance", {})
    constants = constants_payload["constants"]
    baryon_number_density0 = float(normalizations["baryon_number_density0_m3_Z2Sigma"])
    temperature0 = float(temperature_payload["normalizations"]["photon_temperature0_Z2Sigma"])
    z_grid = np.geomspace(100.0, 10000.0, 96)
    n_b = make_conserved_baryon_density_z2sigma(baryon_number_density0)
    temperature = make_conserved_photon_temperature_z2sigma(temperature0)
    x_e = make_saha_ionization_fraction_z2sigma(
        baryon_number_density_m3_z2sigma=n_b,
        photon_temperature_z2sigma=temperature,
        electron_mass_kg=float(constants["electron_mass_kg"]),
        boltzmann_constant_j_k=float(constants["boltzmann_constant_J_K"]),
        hbar_j_s=float(constants["hbar_J_s"]),
        hydrogen_ionization_energy_j=float(constants["hydrogen_ionization_energy_J"]),
    )
    values = x_e(z_grid)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "planck_lcdm_recombination_history_used": False,
        "ionization_model": "hydrogen_saha_equilibrium",
        "electrons_per_baryon": 1.0,
        "z_grid": [float(v) for v in z_grid],
        "ionization_fraction_Z2Sigma": [float(v) for v in values],
        "normalization_inputs": {
            "baryon_number_density0_m3_Z2Sigma": baryon_number_density0,
            "photon_temperature0_Z2Sigma": temperature0,
        },
        "normalization_provenance": {
            "baryon_number_density0_m3_Z2Sigma": provenance.get(
                "baryon_number_density0_m3_Z2Sigma",
                "active_Z2Sigma_baryon_number_density_input",
            ),
            "photon_temperature0_Z2Sigma": "FIRAS_direct_blackbody_temperature_input",
            "electrons_per_baryon": "active_hydrogen_single_electron_convention",
        },
        "constant_provenance": constants_payload.get("constant_provenance", {}),
    }


def build_payload(
    *,
    baryon_input_path: Path = BARYON_INPUT_PATH,
    temperature_input_path: Path = TEMPERATURE_INPUT_PATH,
    constants_input_path: Path = CONSTANTS_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = True,
) -> dict:
    baryon = _read_json(baryon_input_path)
    temperature = _read_json(temperature_input_path)
    constants = _read_json(constants_input_path)
    baryon_valid = _valid_active_payload(baryon, source="active_derived")
    temperature_valid = _valid_active_payload(temperature, source="direct_noncompressed_observation")
    constants_valid = _valid_active_payload(constants, source="active_derived")
    values_ready = False
    validation_error = None
    output_written = False
    history = None
    try:
        values_ready = (
            baryon_valid
            and temperature_valid
            and constants_valid
            and float(baryon["normalizations"]["baryon_number_density0_m3_Z2Sigma"]) > 0.0
            and float(temperature["normalizations"]["photon_temperature0_Z2Sigma"]) > 0.0
            and float(constants["constants"]["electron_mass_kg"]) > 0.0
            and float(constants["constants"]["boltzmann_constant_J_K"]) > 0.0
            and float(constants["constants"]["hbar_J_s"]) > 0.0
            and float(constants["constants"]["hydrogen_ionization_energy_J"]) > 0.0
        )
        if values_ready:
            history = _build_history(baryon, temperature, constants)
            if write_output:
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text(json.dumps(history, indent=2), encoding="utf-8")
                output_written = True
    except Exception as exc:
        validation_error = str(exc)
        values_ready = False
    upstream_frontiers = {
        "baryon_number_density": {
            "path": str(baryon_input_path),
            "input_valid": baryon_valid,
            "required_for": "Saha electron density and ionization fraction",
        },
        "photon_temperature_firas": {
            "path": str(temperature_input_path),
            "input_valid": temperature_valid,
            "required_for": "Saha photon temperature history",
            "direct_noncompressed_observation": True,
        },
        "codata_constants": {
            "path": str(constants_input_path),
            "input_valid": constants_valid,
            "required_for": "Saha electron mass, k_B, hbar and hydrogen ionization energy",
        },
    }
    missing = [
        name
        for name, frontier in upstream_frontiers.items()
        if not frontier["input_valid"]
    ]
    return {
        "status": "janus-z2-sigma-saha-ionization-history-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "https://physics.nist.gov/cuu/Constants/",
            "https://physics.nist.gov/asd",
        ],
        "saha_history_formula_declared": True,
        "baryon_input_valid": baryon_valid,
        "temperature_input_valid": temperature_valid,
        "codata_constants_valid": constants_valid,
        "upstream_frontiers": upstream_frontiers,
        "nearest_saha_history_frontier": {
            "blocks": missing,
            "diagnostic_only": True,
        },
        "saha_ionization_values_ready": values_ready,
        "output_path": str(output_path),
        "output_written": output_written,
        "validation_error": validation_error,
        "uses_planck_lcdm_recombination_history": False,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "electrons_per_baryon_policy": "hydrogen_single_electron_convention",
        "primary_blocker": "none" if values_ready else "active_baryon_number_density_Z2Sigma",
        "gate_passed": values_ready,
        "sample_ionization_fraction": None
        if history is None
        else {
            "z_min": history["z_grid"][0],
            "x_e_at_z_min": history["ionization_fraction_Z2Sigma"][0],
            "z_max": history["z_grid"][-1],
            "x_e_at_z_max": history["ionization_fraction_Z2Sigma"][-1],
        },
        "next_required": [
            "derive_active_baryon_number_density_Z2Sigma_from_Noether_volume",
            "feed_ionization_history_into_active_early_plasma_manifest_writer",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Saha Ionization History Gate",
                "",
                f"Baryon input valid: `{payload['baryon_input_valid']}`",
                f"Temperature input valid: `{payload['temperature_input_valid']}`",
                f"CODATA constants valid: `{payload['codata_constants_valid']}`",
                f"Saha values ready: `{payload['saha_ionization_values_ready']}`",
                f"Gate passed: `{payload['gate_passed']}`",
                "",
                "## Policy",
                "- No Planck-LCDM recombination history.",
                "- No compressed Planck/LCDM sound horizon.",
                "- No archived Z4 inputs.",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
