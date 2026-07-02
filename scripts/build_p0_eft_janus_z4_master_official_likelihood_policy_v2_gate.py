from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_diagnostic_likelihood_trial_v2_gate import (
    build_payload as trial_v2_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_official_likelihood_policy_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_official_likelihood_policy_v2_gate.json")


def build_payload() -> dict:
    trial = trial_v2_payload()
    return {
        "status": "janus-z4-master-official-likelihood-policy-v2-gate",
        "diagnostic_likelihood_trial_v2_passed": trial["diagnostic_likelihood_trial_v2_passed"],
        "diagnostic_trial_uses_observed_planck_data": trial["uses_observed_planck_data"],
        "diagnostic_trial_uses_official_planck_likelihood": trial["uses_official_planck_likelihood"],
        "official_likelihood_policy_declared": True,
        "required_before_official_planck": [
            "observed_planck_likelihood_wrapper_v2",
            "nuisance_foreground_policy_v2",
            "nonoverlap_accounting_policy_v2",
            "GR_reference_handshake_on_same_wrapper_v2",
            "master_v2_no_retuning_replay",
        ],
        "observed_planck_wrapper_declared": False,
        "gr_reference_handshake_on_same_wrapper": False,
        "master_v2_no_retuning_replay": False,
        "official_planck_trial_allowed": False,
        "official_planck_trial_block_reason": "observed_planck_wrapper_gr_handshake_and_no_retuning_replay_not_declared",
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeV2Gate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Official Likelihood Policy V2 Gate",
        "",
        f"Official policy declared: `{payload['official_likelihood_policy_declared']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Block reason: `{payload['official_planck_trial_block_reason']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
