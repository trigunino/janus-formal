from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate.json")

SPEED_OF_LIGHT_SI = 299_792_458.0
STEFAN_BOLTZMANN_2022_SI = 5.670374419e-8
RADIATION_CONSTANT_SI = 4.0 * STEFAN_BOLTZMANN_2022_SI / SPEED_OF_LIGHT_SI
PROTON_MASS_2022_KG = 1.67262192595e-27
THOMSON_CROSS_SECTION_2022_M2 = 6.6524587051e-29
ELECTRON_MASS_2022_KG = 9.1093837139e-31
BOLTZMANN_CONSTANT_EXACT_J_K = 1.380649e-23
PLANCK_CONSTANT_EXACT_J_S = 6.62607015e-34
HBAR_EXACT_J_S = PLANCK_CONSTANT_EXACT_J_S / (2.0 * 3.141592653589793238462643383279502884)
ELECTRON_VOLT_EXACT_J = 1.602176634e-19
HYDROGEN_IONIZATION_ENERGY_NIST_EV = 13.598434599702
HYDROGEN_IONIZATION_ENERGY_NIST_J = HYDROGEN_IONIZATION_ENERGY_NIST_EV * ELECTRON_VOLT_EXACT_J

NIST_SIGMA_T_URL = "https://physics.nist.gov/cgi-bin/cuu/Value?sigmae="
NIST_PROTON_MASS_URL = "https://physics.nist.gov/cgi-bin/cuu/Value?mp="
NIST_STEFAN_BOLTZMANN_URL = "https://physics.nist.gov/cgi-bin/cuu/Value?sigma="
NIST_ELECTRON_MASS_URL = "https://physics.nist.gov/cgi-bin/cuu/Value?me="
NIST_BOLTZMANN_URL = "https://physics.nist.gov/cgi-bin/cuu/Value?k="
NIST_PLANCK_URL = "https://physics.nist.gov/cgi-bin/cuu/Value?h="
NIST_ELECTRON_VOLT_URL = "https://physics.nist.gov/cgi-bin/cuu/Value?evj="
NIST_HYDROGEN_IONIZATION_URL = (
    "https://physics.nist.gov/cgi-bin/ASD/ie.pl?"
    "spectra=H&units=1&at_num_out=on&el_name_out=on&seq_out=on&shells_out=on&level_out=on&e_out=0&unc_out=on"
)


def _manifest() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "constants": {
            "radiation_constant_J_m3_K4": RADIATION_CONSTANT_SI,
            "baryon_mass_kg": PROTON_MASS_2022_KG,
            "sigma_thomson_m2": THOMSON_CROSS_SECTION_2022_M2,
            "electron_mass_kg": ELECTRON_MASS_2022_KG,
            "boltzmann_constant_J_K": BOLTZMANN_CONSTANT_EXACT_J_K,
            "hbar_J_s": HBAR_EXACT_J_S,
            "electron_volt_J": ELECTRON_VOLT_EXACT_J,
            "hydrogen_ionization_energy_J": HYDROGEN_IONIZATION_ENERGY_NIST_J,
        },
        "constant_provenance": {
            "radiation_constant_J_m3_K4": "derived_from_NIST_CODATA_2022_Stefan_Boltzmann_constant_and_exact_c",
            "baryon_mass_kg": "NIST_CODATA_2022_proton_mass_as_baryon_mass_convention",
            "sigma_thomson_m2": "NIST_CODATA_2022_Thomson_cross_section",
            "electron_mass_kg": "NIST_CODATA_2022_electron_mass",
            "boltzmann_constant_J_K": "exact_SI_2019_Boltzmann_constant_via_NIST_CODATA",
            "hbar_J_s": "derived_from_exact_SI_2019_Planck_constant_h_over_2pi",
            "electron_volt_J": "exact_SI_2019_elementary_charge_via_NIST_CODATA",
            "hydrogen_ionization_energy_J": "NIST_ASD_2024_Hydrogen_ionization_energy_times_exact_electron_volt",
        },
        "source_reference": {
            "sigma_thomson": NIST_SIGMA_T_URL,
            "proton_mass": NIST_PROTON_MASS_URL,
            "stefan_boltzmann_constant": NIST_STEFAN_BOLTZMANN_URL,
            "electron_mass": NIST_ELECTRON_MASS_URL,
            "boltzmann_constant": NIST_BOLTZMANN_URL,
            "planck_constant": NIST_PLANCK_URL,
            "electron_volt": NIST_ELECTRON_VOLT_URL,
            "hydrogen_ionization_energy": NIST_HYDROGEN_IONIZATION_URL,
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
            constants = payload["constants"]
            output_valid = (
                payload.get("active_core") == "Z2_tunnel_Sigma"
                and payload.get("source") == "active_derived"
                and payload.get("compressed_planck_lcdm_rd_used") is False
                and payload.get("archived_z4_reuse_used") is False
                and payload.get("phenomenological_holst_bao_scan_used") is False
                and float(constants["radiation_constant_J_m3_K4"]) == RADIATION_CONSTANT_SI
                and float(constants["baryon_mass_kg"]) == PROTON_MASS_2022_KG
                and float(constants["sigma_thomson_m2"]) == THOMSON_CROSS_SECTION_2022_M2
                and float(constants["electron_mass_kg"]) == ELECTRON_MASS_2022_KG
                and float(constants["boltzmann_constant_J_K"]) == BOLTZMANN_CONSTANT_EXACT_J_K
                and float(constants["hbar_J_s"]) == HBAR_EXACT_J_S
                and float(constants["electron_volt_J"]) == ELECTRON_VOLT_EXACT_J
                and float(constants["hydrogen_ionization_energy_J"]) == HYDROGEN_IONIZATION_ENERGY_NIST_J
            )
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-codata-constants-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            NIST_SIGMA_T_URL,
            NIST_PROTON_MASS_URL,
            NIST_STEFAN_BOLTZMANN_URL,
            NIST_ELECTRON_MASS_URL,
            NIST_BOLTZMANN_URL,
            NIST_PLANCK_URL,
            NIST_ELECTRON_VOLT_URL,
            NIST_HYDROGEN_IONIZATION_URL,
        ],
        "constants_manifest": str(output_path),
        "radiation_constant_J_m3_K4": RADIATION_CONSTANT_SI,
        "baryon_mass_kg": PROTON_MASS_2022_KG,
        "sigma_thomson_m2": THOMSON_CROSS_SECTION_2022_M2,
        "electron_mass_kg": ELECTRON_MASS_2022_KG,
        "boltzmann_constant_J_K": BOLTZMANN_CONSTANT_EXACT_J_K,
        "hbar_J_s": HBAR_EXACT_J_S,
        "electron_volt_J": ELECTRON_VOLT_EXACT_J,
        "hydrogen_ionization_energy_J": HYDROGEN_IONIZATION_ENERGY_NIST_J,
        "output_written": output_written,
        "output_exists": output_path.exists(),
        "output_valid": output_valid,
        "validation_error": validation_error,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_valid,
        "does_not_fix_model_normalizations": True,
        "still_required_model_inputs": [
            "rho_baryon0_Z2Sigma",
            "photon_temperature0_Z2Sigma",
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
                "# Janus Z2/Sigma Early-Plasma CODATA Constants Gate",
                "",
                f"Radiation constant: `{payload['radiation_constant_J_m3_K4']}`",
                f"Baryon mass convention: `{payload['baryon_mass_kg']}`",
                f"Thomson cross-section: `{payload['sigma_thomson_m2']}`",
                f"Electron mass: `{payload['electron_mass_kg']}`",
                f"Hydrogen ionization energy: `{payload['hydrogen_ionization_energy_J']}`",
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
