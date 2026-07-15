from __future__ import annotations

import json
import os
from pathlib import Path


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))


def build_payload() -> dict:
    return {
        "artifact": "plugstar_eht_redshift_claim_audit",
        "fit_used": False,
        "source_claim": "ratio of image color-bar extrema interpreted as wavelength ratio near 3",
        "valid_redshift_observable": "ratio of the same identified spectral feature at emitter and observer",
        "logical_gates": {
            "single_frequency_intensity_is_wavelength_measurement": False,
            "brightness_temperature_is_thermodynamic_temperature_without_model": False,
            "intensity_ratio_uniquely_determines_gravitational_redshift": False,
            "radiative_transfer_model_supplied": False,
            "synthetic_visibility_and_reconstruction_pipeline_supplied": False,
        },
        "confounders": [
            "emissivity_and_absorption",
            "electron_distribution_and_temperature",
            "Doppler_beaming",
            "gravitational_lensing",
            "optical_depth",
            "sparse_interferometric_reconstruction",
        ],
        "verdict": "ratio_3_is_not_an_EHT_spectral_redshift_measurement",
        "required_forward_chain": [
            "metric_and_plasma_state",
            "covariant_radiative_transfer",
            "frequency-dependent_specific_intensity",
            "synthetic_complex_visibilities",
            "same_reconstruction_and_summary_statistic_as_data",
        ],
        "primary_context": {
            "eht_data_products": "https://eventhorizontelescope.org/for-astronomers/data",
            "eht_imaging_methods": "https://eventhorizontelescope.org/blog/imaging-reanalyses-eht-data",
            "grmhd_radiative_pipeline": "https://eventhorizontelescope.org/publications/patoka-simulating-electromagnetic-observables-black-hole-accretion",
        },
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "plugstar_eht_redshift_claim.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
