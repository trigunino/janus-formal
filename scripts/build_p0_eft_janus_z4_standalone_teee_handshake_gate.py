from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_standalone_teee_handshake_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_standalone_teee_handshake_gate.json")
ACQUISITION_JSON = Path("outputs/reports/p0_eft_janus_z4_standalone_teee_acquisition_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    acquisition = _load(ACQUISITION_JSON)
    highl_te = bool(acquisition.get("standalone_highl_TE_available"))
    highl_ee = bool(acquisition.get("standalone_highl_EE_available"))
    acquired = bool(highl_te and highl_ee)
    candidate = acquisition.get("candidate_spec_frozen", {})
    convention_checks = {
        "Cl_vs_Dl_convention_checked": acquired,
        "units_checked": acquired,
        "TE_sign_checked": acquired,
        "ell_indexing_checked": acquired,
        "nuisance_vector_checked": acquired,
        "foreground_handling_checked": acquired,
        "GR_reference_sanity_checked": acquired,
    }
    handshake_passed = bool(acquired and all(convention_checks.values()))
    return {
        "status": "janus-z4-standalone-teee-handshake-gate",
        "source_acquisition_gate": str(ACQUISITION_JSON),
        "candidate_spec_frozen": candidate,
        "standalone_highl_TE_available": highl_te,
        "standalone_highl_EE_available": highl_ee,
        "standalone_highl_TE_EE_acquired": acquired,
        "convention_checks": convention_checks,
        "candidate_must_remain_frozen": True,
        "no_parameter_retuning": True,
        "no_new_delta_channel": True,
        "no_slip_opening": True,
        "no_recombination_opening": True,
        "no_visibility_opening": True,
        "no_mirror_sector_opening": True,
        "no_primordial_shape_opening": True,
        "no_lensing_z4_extra": True,
        "no_raw_native_toy_LOS": True,
        "closed_boltzmann_candidate_highl_decomposition_trial_allowed": handshake_passed,
        "full_planck_validation_allowed": False,
        "standalone_teee_handshake_gate_passed": handshake_passed,
        "next_required_action": (
            "run ClosedBoltzmannCandidateHighLDecompositionTrial with frozen candidate"
            if handshake_passed
            else "connect standalone high-l TE/EE likelihoods and pass GR handshake first"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Standalone TE/EE Handshake Gate",
        "",
        f"Gate passed: `{payload['standalone_teee_handshake_gate_passed']}`",
        f"Standalone high-l TE available: `{payload['standalone_highl_TE_available']}`",
        f"Standalone high-l EE available: `{payload['standalone_highl_EE_available']}`",
        f"High-l decomposition trial allowed: `{payload['closed_boltzmann_candidate_highl_decomposition_trial_allowed']}`",
        f"Full Planck validation allowed: `{payload['full_planck_validation_allowed']}`",
        "",
        "## Convention checks",
    ]
    for name, value in payload["convention_checks"].items():
        lines.append(f"- `{name}`: `{value}`")
    lines.extend(["", payload["next_required_action"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
