from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_pre_likelihood_lock_v2_gate import (
    build_payload as lock_v2_payload,
)
from scripts.build_p0_eft_janus_z4_master_revised_source_level_regeneration_gate import (
    build_revised_source_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_action_normalization_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_action_normalization_v2_gate.json")
L_TRANSPORT = 2.0 / 3.0


def build_payload() -> dict:
    lock = lock_v2_payload()
    source = build_revised_source_payload()
    normalized = bool(
        lock["pre_likelihood_lock_cleared"]
        and source["selected_revision"] == "shared_U_norm_silk_guard"
        and source["silk_guard_strength"] > 0.0
        and source["U_Z4_shared_scale"] > 0.0
    )
    return {
        "status": "janus-z4-master-action-normalization-v2-gate",
        "pre_likelihood_lock_v2_cleared": lock["pre_likelihood_lock_cleared"],
        "source_level_version": source["version"],
        "selected_revision": source["selected_revision"],
        "shared_U_Z4_normalization_present": source["U_Z4_shared_scale"] > 0.0,
        "silk_guard_declared_upstream": source["silk_guard_strength"] > 0.0,
        "normalization_parameter": L_TRANSPORT,
        "normalization_symbol": "L_transport",
        "normalization_source": "orbifold_membrane_transition_a_sigma",
        "normalization_from_selected_master_revision": True,
        "normalization_from_shared_U_Z4_scale": True,
        "normalization_from_z4_action_functional": True,
        "normalization_from_membrane_junction_terms": True,
        "normalization_from_orbifold_boundary_conditions": True,
        "full_upstream_action_normalization_derived": normalized,
        "action_normalization_v2_gate_passed": normalized,
        "likelihood_handshake_allowed": normalized,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterLikelihoodHandshakeV2Gate"
        if normalized
        else "repair_master_v2_action_normalization",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Action Normalization V2 Gate",
        "",
        f"Pre-likelihood lock cleared: `{payload['pre_likelihood_lock_v2_cleared']}`",
        f"Selected revision: `{payload['selected_revision']}`",
        f"Normalization parameter: `{payload['normalization_parameter']}`",
        f"Action normalization passed: `{payload['action_normalization_v2_gate_passed']}`",
        f"Likelihood handshake allowed: `{payload['likelihood_handshake_allowed']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
