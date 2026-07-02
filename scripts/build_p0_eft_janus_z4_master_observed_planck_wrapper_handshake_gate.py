from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_standalone_teee_acquisition_gate import _channel_locator


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_wrapper_handshake_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_wrapper_handshake_gate.json")
GR_HANDSHAKE_JSON = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_gr_reference_handshake.json")
POLICY_JSON = Path("outputs/reports/p0_eft_janus_z4_master_official_likelihood_policy_gate.json")

REQUIRED_COMPONENTS = ("highl_TTTEEE", "highl_TE", "highl_EE", "lowl_TT", "lowl_EE", "lensing")


def _combined_locator() -> dict:
    highl_root = Path(".venv-cosmo/Lib/site-packages/cobaya/likelihoods/planck_2018_highl_plik")
    data_root = Path("external/cobaya_packages/data")
    expected = "plik_rd12_HM_v22b_TTTEEE.clik"
    matches = sorted(str(path) for path in data_root.rglob(expected)) if data_root.exists() else []
    return {
        "cobaya_component": "planck_2018_highl_plik.TTTEEE",
        "wrapper_py": str(highl_root / "TTTEEE.py"),
        "wrapper_yaml": str(highl_root / "TTTEEE.yaml"),
        "wrapper_present": (highl_root / "TTTEEE.py").exists() and (highl_root / "TTTEEE.yaml").exists(),
        "expected_clik_name": expected,
        "expected_clik_paths_found": matches,
        "clik_data_present": bool(matches),
        "available": bool((highl_root / "TTTEEE.py").exists() and (highl_root / "TTTEEE.yaml").exists() and matches),
    }


def _simple_component(name: str, wrapper_root: Path, data_root: Path, module_stub: str, expected_suffix: str) -> dict:
    wrapper_py = wrapper_root / f"{module_stub}.py"
    wrapper_yaml = wrapper_root / f"{module_stub}.yaml"
    matches = sorted(str(path) for path in data_root.rglob(expected_suffix)) if data_root.exists() else []
    return {
        "cobaya_component": name,
        "wrapper_py": str(wrapper_py),
        "wrapper_yaml": str(wrapper_yaml),
        "wrapper_present": wrapper_py.exists() and wrapper_yaml.exists(),
        "expected_data_name": expected_suffix,
        "data_paths_found": matches,
        "data_present": bool(matches),
        "available": bool(wrapper_py.exists() and wrapper_yaml.exists() and matches),
    }


def _component_locators() -> dict:
    lowl_root = Path(".venv-cosmo/Lib/site-packages/cobaya/likelihoods/planck_2018_lowl")
    lensing_root = Path(".venv-cosmo/Lib/site-packages/cobaya/likelihoods/planck_2018_lensing")
    data_root = Path("external/cobaya_packages/data")
    return {
        "highl_TTTEEE": _combined_locator(),
        "highl_TE": _channel_locator("TE"),
        "highl_EE": _channel_locator("EE"),
        "lowl_TT": _simple_component(
            "planck_2018_lowl.TT_clik",
            lowl_root,
            data_root,
            "TT_clik",
            "commander_dx12_v3_2_29.clik",
        ),
        "lowl_EE": _simple_component(
            "planck_2018_lowl.EE_clik",
            lowl_root,
            data_root,
            "EE_clik",
            "simall_100x143_offlike5_EE_Aplanck_B.clik",
        ),
        "lensing": _simple_component(
            "planck_2018_lensing.clik",
            lensing_root,
            data_root,
            "clik",
            "smicadx12_Dec5_ftl_mv2_ndclpp_p_teb_consext8.clik_lensing",
        ),
    }


def _load_gr_handshake() -> dict:
    return json.loads(GR_HANDSHAKE_JSON.read_text(encoding="utf-8")) if GR_HANDSHAKE_JSON.exists() else {}


def _policy_declared() -> bool:
    if not POLICY_JSON.exists():
        return True
    policy = json.loads(POLICY_JSON.read_text(encoding="utf-8"))
    return bool(policy.get("official_likelihood_policy_declared"))


def build_payload() -> dict:
    locators = _component_locators()
    gr = _load_gr_handshake()
    available = {name: bool(locators[name]["available"]) for name in REQUIRED_COMPONENTS}
    observed_wrapper_available = all(available.values())
    gr_checks = {
        "Cl_vs_Dl_convention_checked": bool(gr.get("Cl_vs_Dl_convention_checked")),
        "units_checked": bool(gr.get("units_checked")),
        "TE_sign_checked": bool(gr.get("TE_sign_checked")),
        "ell_indexing_checked": bool(gr.get("ell_indexing_checked")),
        "nuisance_vector_checked": bool(gr.get("nuisance_vector_checked")),
        "foreground_handling_checked": bool(gr.get("foreground_handling_checked")),
        "GR_reference_sanity_checked": bool(gr.get("GR_reference_sanity_checked")),
    }
    gr_handshake_passed = bool(observed_wrapper_available and all(gr_checks.values()))
    policy_declared = _policy_declared()
    return {
        "status": "janus-z4-master-observed-planck-wrapper-handshake-gate",
        "official_likelihood_policy_declared": policy_declared,
        "source_policy_gate": str(POLICY_JSON),
        "component_availability": available,
        "component_locators": locators,
        "observed_planck_wrapper_available": observed_wrapper_available,
        "mock_wrappers_allowed": False,
        "fallback_to_internal_pseudo_likelihood_allowed": False,
        "gr_reference_handshake_report_present": bool(gr),
        "gr_reference_handshake_checks": gr_checks,
        "gr_reference_handshake_on_same_wrapper_passed": gr_handshake_passed,
        "master_candidate_no_retuning_replay": False,
        "observed_planck_wrapper_handshake_gate_passed": bool(policy_declared and gr_handshake_passed),
        "official_planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "next_required_gate": "provide_master_observed_planck_gr_reference_handshake"
        if not gr_handshake_passed
        else "P0EFTJanusZ4MasterNoRetuningReplayGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Observed Planck Wrapper Handshake Gate",
        "",
        f"Observed wrapper available: `{payload['observed_planck_wrapper_available']}`",
        f"GR handshake present: `{payload['gr_reference_handshake_report_present']}`",
        f"Gate passed: `{payload['observed_planck_wrapper_handshake_gate_passed']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
