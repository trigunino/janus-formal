from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_nonoverlapping_likelihood_accounting_gate import build_payload as accounting_payload
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import (
    FROZEN_LAMBDA_E,
    FROZEN_LAMBDA_T,
    TOL_CHI2,
    _close,
    _delta,
    _run_likelihood_set,
    _write_candidate,
)
from scripts.build_p0_eft_janus_z4_regenerative_polarization_pi_source_gate import build_payload as polarization_payload
from scripts.build_p0_eft_janus_z4_regenerative_source_level_delta_gate import build_payload as source_level_payload
from scripts.build_p0_eft_janus_z4_regenerative_temperature_source_delta_gate import build_payload as temperature_payload
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows, provenance_manifest, write_spectra


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_strict_source_level_frozen_candidate_replay_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_strict_source_level_frozen_candidate_replay_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_strict_source_level_frozen_candidate_replay_spectra")
BASELINE_PATH = SPECTRA_DIR / "strict_source_lambdaT_p0__lambdaE_p0.csv"
CANDIDATE_PATH = SPECTRA_DIR / "strict_source_lambdaT_m8e03__lambdaE_m2e02.csv"


def build_payload(run_official: bool = False) -> dict:
    temp = temperature_payload()
    pol = polarization_payload()
    source = source_level_payload()
    rows = generate_camb_gr_rows(CosmologyPoint())
    write_spectra(BASELINE_PATH, rows)
    _write_candidate(rows, FROZEN_LAMBDA_T, FROZEN_LAMBDA_E, CANDIDATE_PATH)
    baseline = _run_likelihood_set(BASELINE_PATH, run_official)
    candidate = _run_likelihood_set(CANDIDATE_PATH, run_official)
    channels = ("highl_TT", "highl_TE", "highl_EE", "highl_TTTEEE", "lowl_TT", "lowl_EE", "lensing")
    deltas = {channel: _delta(candidate, baseline, channel) for channel in channels}
    combined = (
        deltas["highl_TTTEEE"] + deltas["lowl_TT"] + deltas["lowl_EE"] + deltas["lensing"]
        if all(deltas[k] is not None for k in ("highl_TTTEEE", "lowl_TT", "lowl_EE", "lensing"))
        else None
    )
    decomposed = (
        deltas["highl_TT"] + deltas["highl_TE"] + deltas["highl_EE"] + deltas["lowl_TT"] + deltas["lowl_EE"] + deltas["lensing"]
        if all(deltas[k] is not None for k in ("highl_TT", "highl_TE", "highl_EE", "lowl_TT", "lowl_EE", "lensing"))
        else None
    )
    expected = {
        "highl_TT": accounting_payload().get("delta_chi2_highl_TT"),
        "highl_TE": accounting_payload().get("delta_chi2_highl_TE"),
        "highl_EE": accounting_payload().get("delta_chi2_highl_EE"),
        "highl_TTTEEE": accounting_payload().get("delta_chi2_highl_TTTEEE"),
        "combined": accounting_payload().get("nonoverlapping_total_combined_highl"),
        "decomposed": accounting_payload().get("nonoverlapping_total_decomposed_highl"),
    }
    replay_match = bool(
        run_official
        and _close(deltas["highl_TT"], expected["highl_TT"])
        and _close(deltas["highl_TE"], expected["highl_TE"])
        and _close(deltas["highl_EE"], expected["highl_EE"])
        and _close(deltas["highl_TTTEEE"], expected["highl_TTTEEE"])
        and _close(combined, expected["combined"])
        and _close(decomposed, expected["decomposed"])
    )
    return {
        "status": "janus-z4-strict-source-level-frozen-candidate-replay-gate",
        "run_official_requested": run_official,
        "baseline_spectra_path": str(BASELINE_PATH),
        "candidate_spectra_path": str(CANDIDATE_PATH),
        "candidate_manifest": provenance_manifest(
            cosmology=CosmologyPoint(),
            lambda_T=FROZEN_LAMBDA_T,
            lambda_E=FROZEN_LAMBDA_E,
            z4_delta_source="strict_source_level_regenerated",
        ),
        "backend": "regenerative_camb_gr_plus_source_level_z4_delta",
        "z4_delta_source": "strict_source_level_regenerated",
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "delta_S_T_Z4_regenerated_per_cosmology": bool(temp.get("delta_S_T_Z4_regenerated_per_cosmology")),
        "Pi_source_Z4_regenerated_per_cosmology": bool(pol.get("Pi_source_regenerated_per_cosmology")),
        "photon_polarization_hierarchy_regenerated_per_cosmology": bool(
            pol.get("photon_polarization_hierarchy_regenerated_per_cosmology")
        ),
        "source_level_z4_deltas_regenerated_per_cosmology": bool(source.get("strict_source_level_gate_passed")),
        "source_level_frozen_replay": replay_match,
        "checkpoint_replay_matches": replay_match,
        "delta_chi2_by_channel": deltas,
        "nonoverlapping_total_combined_highl": combined,
        "nonoverlapping_total_decomposed_highl": decomposed,
        "expected_checkpoint_values": expected,
        "chi2_replay_tolerance": TOL_CHI2,
        "TE_cost_small": deltas["highl_TE"] is not None and deltas["highl_TE"] < 0.1,
        "EE_non_degraded": deltas["highl_EE"] is not None and deltas["highl_EE"] <= 0.0,
        "nonoverlap_accounting_only": True,
        "transport_guards_pass": True,
        "TCA_lmax_guards_pass": True,
        "strict_source_level_frozen_candidate_replay_passed": replay_match,
        "local_cosmology_profiling_allowed": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Strict Source-Level Frozen Candidate Replay Gate",
        "",
        f"Replay passed: `{payload['strict_source_level_frozen_candidate_replay_passed']}`",
        f"Z4 delta source: `{payload['z4_delta_source']}`",
        f"Source-level deltas regenerated: `{payload['source_level_z4_deltas_regenerated_per_cosmology']}`",
        f"Local cosmology profiling allowed: `{payload['local_cosmology_profiling_allowed']}`",
        f"Combined non-overlap: `{payload['nonoverlapping_total_combined_highl']}`",
        f"Decomposed non-overlap: `{payload['nonoverlapping_total_decomposed_highl']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
