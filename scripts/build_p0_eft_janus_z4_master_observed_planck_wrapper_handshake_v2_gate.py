from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_observed_planck_wrapper_handshake_gate import (
    REQUIRED_COMPONENTS,
    _component_locators,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_wrapper_handshake_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_wrapper_handshake_v2_gate.json")
GR_HANDSHAKE_JSON = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_gr_reference_handshake_v2.json")
POLICY_JSON = Path("outputs/reports/p0_eft_janus_z4_master_official_likelihood_policy_v2_gate.json")


def _load_gr_handshake() -> dict:
    return json.loads(GR_HANDSHAKE_JSON.read_text(encoding="utf-8")) if GR_HANDSHAKE_JSON.exists() else {}


def _policy_declared() -> bool:
    if not POLICY_JSON.exists():
        return False
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
    gr_passed = bool(observed_wrapper_available and all(gr_checks.values()))
    policy_declared = _policy_declared()
    gate_passed = bool(policy_declared and gr_passed)
    return {
        "status": "janus-z4-master-observed-planck-wrapper-handshake-v2-gate",
        "official_likelihood_policy_v2_declared": policy_declared,
        "source_policy_gate": str(POLICY_JSON),
        "component_availability": available,
        "component_locators": locators,
        "observed_planck_wrapper_available": observed_wrapper_available,
        "mock_wrappers_allowed": False,
        "fallback_to_internal_pseudo_likelihood_allowed": False,
        "gr_reference_handshake_v2_report_present": bool(gr),
        "gr_reference_handshake_v2_checks": gr_checks,
        "gr_reference_handshake_on_same_wrapper_v2_passed": gr_passed,
        "master_v2_no_retuning_replay": False,
        "observed_planck_wrapper_handshake_v2_gate_passed": gate_passed,
        "official_planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterNoRetuningReplayV2Gate"
        if gate_passed
        else "provide_master_observed_planck_gr_reference_handshake_v2",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Observed Planck Wrapper Handshake V2 Gate",
        "",
        f"Observed wrapper available: `{payload['observed_planck_wrapper_available']}`",
        f"GR handshake present: `{payload['gr_reference_handshake_v2_report_present']}`",
        f"Gate passed: `{payload['observed_planck_wrapper_handshake_v2_gate_passed']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
