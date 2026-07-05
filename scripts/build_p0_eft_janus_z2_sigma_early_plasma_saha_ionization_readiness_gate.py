from __future__ import annotations

import json
from pathlib import Path


BARYON_MODEL_INPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_baryon_number_density_noether_volume_inputs.json"
)
PHOTON_TEMPERATURE_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_saha_ionization_readiness_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_saha_ionization_readiness_gate.json"
)

PEEBLES_1968_ADS = "https://adsabs.harvard.edu/full/1968ApJ...153....1P"
SEAGER_1999_ADS = "https://ui.adsabs.harvard.edu/abs/1999ApJ...523L...1S/abstract"
RECFAST_REFERENCE = "https://www.astro.ubc.ca/people/scott/recfast.html"


def _valid_model_baryon_number(path: Path) -> bool:
    if not path.exists():
        return False
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        return (
            payload.get("active_core") == "Z2_tunnel_Sigma"
            and payload.get("source") == "active_derived"
            and float(payload["normalizations"]["baryon_number_density0_m3_Z2Sigma"]) > 0.0
            and payload.get("compressed_planck_lcdm_rd_used") is False
            and payload.get("archived_z4_reuse_used") is False
            and payload.get("phenomenological_holst_bao_scan_used") is False
        )
    except Exception:
        return False


def _valid_temperature(path: Path) -> bool:
    if not path.exists():
        return False
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        return (
            payload.get("active_core") == "Z2_tunnel_Sigma"
            and payload.get("source") == "direct_noncompressed_observation"
            and float(payload["normalizations"]["photon_temperature0_Z2Sigma"]) > 0.0
        )
    except Exception:
        return False


def build_payload(
    *,
    baryon_model_input_path: Path = BARYON_MODEL_INPUT_PATH,
    photon_temperature_path: Path = PHOTON_TEMPERATURE_PATH,
) -> dict:
    baryon_number_valid = _valid_model_baryon_number(baryon_model_input_path)
    temperature_valid = _valid_temperature(photon_temperature_path)
    values_ready = baryon_number_valid and temperature_valid
    return {
        "status": "janus-z2-sigma-early-plasma-saha-ionization-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            PEEBLES_1968_ADS,
            SEAGER_1999_ADS,
            RECFAST_REFERENCE,
        ],
        "saha_equilibrium_formula_declared": True,
        "formula": "x_e^2/(1-x_e)=n_b(z)^-1*(m_e*k_B*T_gamma(z)/(2*pi*hbar^2))^(3/2)*exp(-E_H/(k_B*T_gamma(z)))",
        "temperature_input_valid": temperature_valid,
        "active_baryon_number_input_valid": baryon_number_valid,
        "saha_ionization_values_ready": values_ready,
        "full_peebles_recfast_history_ready": False,
        "uses_planck_lcdm_recombination_history": False,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": values_ready,
        "next_required": [
            "derive_active_baryon_number_density_Z2Sigma",
            "upgrade_from_Saha_equilibrium_to_Peebles_or_RECFAST_if_precision_required",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Saha Ionization Readiness Gate",
                "",
                f"Saha formula declared: `{payload['saha_equilibrium_formula_declared']}`",
                f"Values ready: `{payload['saha_ionization_values_ready']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
