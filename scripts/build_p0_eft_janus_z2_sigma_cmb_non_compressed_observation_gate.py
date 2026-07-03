from __future__ import annotations

import json
from pathlib import Path


PLANCK_PATHS = {
    "planck_low_l_commander_available": Path(
        "external/cobaya_packages/data/planck_2018/baseline/plc_3.0/low_l/commander/commander_dx12_v3_2_29.clik"
    ),
    "planck_low_e_simall_available": Path(
        "external/cobaya_packages/data/planck_2018/baseline/plc_3.0/low_l/simall/simall_100x143_offlike5_EE_Aplanck_B.clik"
    ),
    "planck_high_l_ttteee_available": Path(
        "external/cobaya_packages/data/planck_2018/extended_plik/plc_3.0/hi_l/plik/plik_rd12_HM_v22b_TTTEEE_bin1.clik"
    ),
    "planck_lensing_available": Path(
        "external/cobaya_packages/data/planck_2018/baseline/plc_3.0/lensing/smicadx12_Dec5_ftl_mv2_ndclpp_p_teb_consext8_CMBmarged.clik_lensing"
    ),
}
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cmb_non_compressed_observation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cmb_non_compressed_observation_gate.json")


def build_payload() -> dict:
    likelihoods = {name: path.exists() for name, path in PLANCK_PATHS.items()}
    prerequisites = {
        "cmb_boltzmann_equations_derived": True,
        **likelihoods,
        "compressed_lcdm_planck_priors_forbidden": True,
        "archived_z4_cmb_spectra_reuse_forbidden": True,
    }
    prediction = {
        "z2_sigma_cmb_theory_spectra_ready": False,
        "planck_likelihood_evaluated_on_z2_sigma_spectra": False,
    }
    return {
        "status": "janus-z2-sigma-cmb-non-compressed-observation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "non_compressed_planck_likelihoods": {name: str(path) for name, path in PLANCK_PATHS.items()},
        "prerequisites": prerequisites,
        "prediction": prediction,
        "cmb_observation_prerequisites_ready": all(prerequisites.values()),
        "cmb_non_compressed_gate_passed": all(prerequisites.values()) and all(prediction.values()),
        "full_cosmology_prediction_ready_no_fit": False,
        "forbidden_reuse": [
            "processed_planck2018_lcdm_priors",
            "archived_z4_cmb_spectra",
            "archived_camb_janus_fork_verdicts",
        ],
        "next_required": [
            "generate_z2_sigma_TT_TE_EE_PP_spectra_from_derived_boltzmann_equations",
            "handshake_z2_sigma_spectra_units_and_ell_conventions",
            "evaluate_non_compressed_planck_likelihoods_on_z2_sigma_spectra",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma CMB Non-Compressed Observation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Bibliography checked: `{payload['bibliography_checked']}`",
        f"CMB prerequisites ready: `{payload['cmb_observation_prerequisites_ready']}`",
        f"Z2/Sigma theory spectra ready: `{payload['prediction']['z2_sigma_cmb_theory_spectra_ready']}`",
        f"CMB non-compressed gate passed: `{payload['cmb_non_compressed_gate_passed']}`",
        "",
        "## Non-Compressed Planck Likelihoods",
    ]
    lines.extend(
        f"- `{name}`: `{payload['prerequisites'][name]}`"
        for name in PLANCK_PATHS
    )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
