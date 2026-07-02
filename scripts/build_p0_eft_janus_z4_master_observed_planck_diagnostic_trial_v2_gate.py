from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_no_retuning_replay_v2_gate import (
    build_payload as replay_v2_payload,
)
from scripts.build_p0_eft_janus_z4_master_observed_planck_diagnostic_trial_gate import (
    CHANNELS,
    _delta,
    _evaluate,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_diagnostic_trial_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_diagnostic_trial_v2_gate.json")


def build_payload(run_observed: bool = False) -> dict:
    replay = replay_v2_payload()
    allowed = bool(replay["candidate_replayed_without_retuning"])
    baseline_path = Path(replay["baseline_spectra_path"])
    candidate_path = Path(replay["candidate_spectra_path"])
    execute = bool(run_observed and allowed)
    baseline = _evaluate(baseline_path, execute)
    candidate = _evaluate(candidate_path, execute)
    deltas = {channel: _delta(candidate, baseline, channel) for channel in CHANNELS}
    finite = [value for value in deltas.values() if value is not None]
    combined = (
        deltas["highl_TTTEEE"] + deltas["lowl_TT"] + deltas["lowl_EE"] + deltas["lensing"]
        if all(deltas[k] is not None for k in ("highl_TTTEEE", "lowl_TT", "lowl_EE", "lensing"))
        else None
    )
    decomposed = (
        deltas["highl_TT"]
        + deltas["highl_TE"]
        + deltas["highl_EE"]
        + deltas["lowl_TT"]
        + deltas["lowl_EE"]
        + deltas["lensing"]
        if all(deltas[k] is not None for k in ("highl_TT", "highl_TE", "highl_EE", "lowl_TT", "lowl_EE", "lensing"))
        else None
    )
    clean_nonoverlap = bool(
        execute
        and combined is not None
        and decomposed is not None
        and combined < 0.0
        and decomposed < 0.0
    )
    return {
        "status": "janus-z4-master-observed-planck-diagnostic-trial-v2-gate",
        "no_retuning_replay_v2_gate_passed": allowed,
        "run_observed_requested": run_observed,
        "run_observed_executed": execute,
        "baseline_spectra_path": str(baseline_path),
        "candidate_spectra_path": str(candidate_path),
        "baseline": baseline,
        "candidate": candidate,
        "delta_chi2_by_channel": deltas,
        "legacy_overlapping_total": float(sum(finite)) if len(finite) == len(CHANNELS) else None,
        "nonoverlapping_total_combined_highl": combined,
        "nonoverlapping_total_decomposed_highl": decomposed,
        "nonoverlap_accounting_required": True,
        "clean_nonoverlap_result": clean_nonoverlap,
        "diagnostic_trial_allowed": allowed,
        "diagnostic_trial_passed": bool(allowed and (not execute or clean_nonoverlap)),
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterObservedNonOverlapAccountingV2Gate"
        if execute
        else "run_with_observed_planck_explicitly_if_requested",
    }


def write_reports(run_observed: bool = False) -> dict:
    payload = build_payload(run_observed=run_observed)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Observed Planck Diagnostic Trial V2 Gate",
        "",
        f"Observed run requested: `{payload['run_observed_requested']}`",
        f"Observed run executed: `{payload['run_observed_executed']}`",
        f"Clean non-overlap result: `{payload['clean_nonoverlap_result']}`",
        f"Candidate promotion allowed: `{payload['candidate_promotion_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_observed=False), indent=2))
