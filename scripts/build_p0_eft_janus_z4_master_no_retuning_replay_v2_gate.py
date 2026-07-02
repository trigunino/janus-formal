from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_observed_planck_wrapper_handshake_v2_gate import (
    build_payload as wrapper_v2_payload,
)
from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_spectra_v2_gate import (
    build_payload as spectra_v2_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_no_retuning_replay_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_no_retuning_replay_v2_gate.json")


def build_payload() -> dict:
    wrapper = wrapper_v2_payload()
    spectra = spectra_v2_payload()
    baseline_exists = Path(spectra["baseline_spectra_path"]).exists()
    candidate_exists = Path(spectra["candidate_spectra_path"]).exists()
    replay_passed = bool(
        wrapper["observed_planck_wrapper_handshake_v2_gate_passed"]
        and spectra["diagnostic_spectra_v2_generated"]
        and spectra["passes_carrier_threshold_lt_0p7"]
        and baseline_exists
        and candidate_exists
    )
    return {
        "status": "janus-z4-master-no-retuning-replay-v2-gate",
        "observed_planck_wrapper_handshake_v2_gate_passed": wrapper[
            "observed_planck_wrapper_handshake_v2_gate_passed"
        ],
        "source_level_version": spectra["source_level_version"],
        "source_payload_hash": spectra["source_payload_hash"],
        "normalization_fixed_to_a_sigma": True,
        "selected_revision_fixed": "shared_U_norm_silk_guard",
        "baseline_spectra_path": spectra["baseline_spectra_path"],
        "candidate_spectra_path": spectra["candidate_spectra_path"],
        "baseline_spectra_exists": baseline_exists,
        "candidate_spectra_exists": candidate_exists,
        "carrier_threshold_passed": spectra["passes_carrier_threshold_lt_0p7"],
        "lambda_retuning_allowed": False,
        "normalization_retuning_allowed": False,
        "revision_retuning_allowed": False,
        "new_physics_channel_allowed": False,
        "candidate_replayed_without_retuning": replay_passed,
        "official_planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterObservedPlanckDiagnosticTrialV2Gate"
        if replay_passed
        else "repair_master_no_retuning_replay_v2",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master No-Retuning Replay V2 Gate",
        "",
        f"Replay without retuning: `{payload['candidate_replayed_without_retuning']}`",
        f"Selected revision fixed: `{payload['selected_revision_fixed']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
