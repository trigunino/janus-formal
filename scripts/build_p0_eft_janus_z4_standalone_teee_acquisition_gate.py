from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_standalone_teee_acquisition_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_standalone_teee_acquisition_gate.json")
COMPLETENESS_JSON = Path("outputs/reports/p0_eft_janus_z4_planck_likelihood_completeness_gate.json")
ROBUSTNESS_JSON = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_robustness_gate.json")
PLIK_WRAPPER_ROOT = Path(".venv-cosmo/Lib/site-packages/cobaya/likelihoods/planck_2018_highl_plik")
PLANCK_DATA_ROOT = Path("external/cobaya_packages/data")
EXPECTED_CLIK = {
    "TE": "plik_rd12_HM_v22_TE.clik",
    "EE": "plik_rd12_HM_v22_EE.clik",
}


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _channel_locator(channel: str) -> dict:
    wrapper_py = PLIK_WRAPPER_ROOT / f"{channel}.py"
    wrapper_yaml = PLIK_WRAPPER_ROOT / f"{channel}.yaml"
    expected_name = EXPECTED_CLIK[channel]
    matches = sorted(str(path) for path in PLANCK_DATA_ROOT.rglob(expected_name)) if PLANCK_DATA_ROOT.exists() else []
    return {
        "cobaya_component": f"planck_2018_highl_plik.{channel}",
        "wrapper_py": str(wrapper_py),
        "wrapper_yaml": str(wrapper_yaml),
        "wrapper_present": wrapper_py.exists() and wrapper_yaml.exists(),
        "expected_clik_name": expected_name,
        "expected_clik_paths_found": matches,
        "clik_data_present": bool(matches),
        "available": bool(wrapper_py.exists() and wrapper_yaml.exists() and matches),
    }


def build_payload() -> dict:
    completeness = _load(COMPLETENESS_JSON)
    robustness = _load(ROBUSTNESS_JSON)
    standalone_locator = {channel: _channel_locator(channel) for channel in ("TE", "EE")}
    frozen_candidate = {
        "candidate_name": "P0EFTJanusZ4ClosedBoltzmannAcousticPolarizationCandidate",
        "backend": "camb_gr_plus_z4_delta",
        "temperature_component": "early_isw_only",
        "lambda_T": -8.0e-3,
        "polarization_component": "closed photon/polarization Boltzmann hierarchy",
        "lambda_E": -2.0e-2,
        "recombination_frozen": True,
        "visibility_frozen": True,
        "background_projection_frozen": True,
        "r_s_frozen": True,
        "r_d_frozen": True,
        "primordial_spectrum_frozen": True,
        "lensing_C_phi_phi_frozen": True,
        "slip_frozen": True,
        "mirror_negative_sector_boltzmann_frozen": True,
        "raw_native_toy_LOS_forbidden": True,
    }
    highl_te = bool(completeness.get("highl_TE_standalone_available")) or standalone_locator["TE"]["available"]
    highl_ee = bool(completeness.get("highl_EE_standalone_available")) or standalone_locator["EE"]["available"]
    robust_candidate = bool(robustness.get("closed_boltzmann_candidate_robustness_gate_passed"))
    return {
        "status": "janus-z4-standalone-teee-acquisition-gate",
        "candidate_spec_frozen": frozen_candidate,
        "standalone_likelihood_locator": standalone_locator,
        "robust_available_channel_candidate": robust_candidate,
        "standalone_highl_TE_available": highl_te,
        "standalone_highl_EE_available": highl_ee,
        "standalone_highl_TE_EE_acquired": bool(highl_te and highl_ee),
        "candidate_must_remain_frozen_for_next_trial": True,
        "no_parameter_retuning": True,
        "no_new_delta_channel": True,
        "no_slip_opening": True,
        "no_recombination_opening": True,
        "no_visibility_opening": True,
        "no_mirror_sector_opening": True,
        "no_primordial_shape_opening": True,
        "no_raw_native_toy_LOS": True,
        "next_trial_name": "official_planck_closed_boltzmann_candidate_full_highl_decomposition_trial",
        "required_future_outputs": [
            "delta_chi2_highl_TT",
            "delta_chi2_highl_TE",
            "delta_chi2_highl_EE",
            "delta_chi2_highl_TTTEEE",
            "delta_chi2_lowl_TT",
            "delta_chi2_lowl_EE",
            "delta_chi2_lensing",
            "delta_chi2_total",
            "TE_zero_guards",
            "EE_peak_guards",
            "TE_residual_smoothness",
            "EE_residual_smoothness",
            "lmax_convergence",
            "TCA_switch_smoothness",
        ],
        "full_highl_decomposition_trial_allowed": False,
        "full_planck_validation_allowed": False,
        "standalone_teee_acquisition_gate_passed": robust_candidate,
        "next_required_action": (
            "run standalone high-l TE/EE GR handshake before rerunning the frozen candidate"
            if robust_candidate and highl_te and highl_ee
            else "acquire standalone high-l TE/EE likelihoods, then run GR handshake"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Standalone TE/EE Acquisition Gate",
        "",
        f"Gate passed: `{payload['standalone_teee_acquisition_gate_passed']}`",
        f"Robust available-channel candidate: `{payload['robust_available_channel_candidate']}`",
        f"Standalone high-l TE available: `{payload['standalone_highl_TE_available']}`",
        f"Standalone high-l EE available: `{payload['standalone_highl_EE_available']}`",
        f"Full high-l decomposition trial allowed: `{payload['full_highl_decomposition_trial_allowed']}`",
        f"Full Planck validation allowed: `{payload['full_planck_validation_allowed']}`",
        "",
        "## Local locator",
        "",
    ]
    for channel, info in payload["standalone_likelihood_locator"].items():
        lines.extend([
            f"### {channel}",
            f"- Cobaya wrapper present: `{info['wrapper_present']}`",
            f"- Expected clik: `{info['expected_clik_name']}`",
            f"- clik data present: `{info['clik_data_present']}`",
            f"- available: `{info['available']}`",
            "",
        ])
    lines.extend([
        payload["next_required_action"],
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
