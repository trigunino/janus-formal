from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_minus_sector_microphysics_specification_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_minus_sector_microphysics_specification_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z4-minus-sector-microphysics-specification-gate",
        "previous_minus_transfer_rank1_diagnosis": True,
        "minus_sector_amplitude_like_archived": True,
        "required_non_amplitude_microphysics": [
            "sound_speed_or_jeans_scale",
            "pressure_law",
            "shear_or_free_streaming",
            "thermal_ratio",
            "decoupling_law",
            "mirror_radiation_hierarchy",
            "effective_mass_or_jeans_scale",
        ],
        "first_test_route": "sound_speed_jeans",
        "thermodynamic_density_sign_separate_from_gravitational_sign": True,
        "bianchi_conservation_required": True,
        "Q_plus_zero_until_exchange_law_derived": True,
        "Q_minus_zero_until_exchange_law_derived": True,
        "minus_sector_amplitude_knob_allowed": False,
        "rho_eff_shortcut_allowed": False,
        "projection_only_fix_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "Planck_trial_allowed": False,
        "spectra_generation_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MinusSectorSoundSpeedJeansGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Minus-Sector Microphysics Specification Gate",
        "",
        f"Previous rank-1 diagnosis: `{payload['previous_minus_transfer_rank1_diagnosis']}`",
        f"First route: `{payload['first_test_route']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
