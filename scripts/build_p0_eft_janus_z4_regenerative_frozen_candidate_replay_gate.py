from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_nonoverlapping_likelihood_accounting_gate import build_payload as accounting_payload
from scripts.build_p0_eft_janus_z4_teee_transport_smoothness_gate import _tight_coupling_projected_response
from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import _transfer_response
from scripts.run_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial import (
    _run_likelihood_set,
)
from janus_lab.z4_regenerative_camb_provider import (
    CosmologyPoint,
    FIELDS,
    generate_camb_gr_rows,
    provenance_manifest,
    write_spectra,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_regenerative_frozen_candidate_replay_spectra")
BASELINE_PATH = SPECTRA_DIR / "regenerated_lambdaT_p0__lambdaE_p0.csv"
CANDIDATE_PATH = SPECTRA_DIR / "regenerated_lambdaT_m8e03__lambdaE_m2e02.csv"
FROZEN_LAMBDA_T = -8.0e-3
FROZEN_LAMBDA_E = -2.0e-2
TOL_CHI2 = 1.0e-6


def _hierarchy_closed_response(ell: np.ndarray) -> np.ndarray:
    base = _tight_coupling_projected_response(ell)
    lmax24_projection = 1.0 - 0.006 * np.exp(-np.square((ell - 1700.0) / 700.0))
    transition_smoothing = 1.0 - 0.004 * np.exp(-np.square((ell - 70.0) / 55.0))
    return base * lmax24_projection * transition_smoothing


def _write_candidate(rows: list[dict[str, float]], lambda_t: float, lambda_e: float, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    ell = np.array([row["ell"] for row in rows], dtype=float)
    temp_factor = 1.0 + lambda_t * _transfer_response(ell, "early_isw_only")
    e_factor = 1.0 + lambda_e * _hierarchy_closed_response(ell)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        for row, tf, ef in zip(rows, temp_factor, e_factor):
            writer.writerow(
                {
                    "ell": int(row["ell"]),
                    "cl_tt": row["cl_tt"] * tf * tf,
                    "cl_te": row["cl_te"] * tf * ef,
                    "cl_ee": row["cl_ee"] * ef * ef,
                    "cl_pp": row["cl_pp"],
                }
            )


def _delta(candidate: dict, baseline: dict, channel: str) -> float | None:
    c = candidate.get("finite_channel_chi2", {}).get(channel)
    b = baseline.get("finite_channel_chi2", {}).get(channel)
    return float(c - b) if c is not None and b is not None else None


def _close(actual: float | None, expected: float | None) -> bool:
    return actual is not None and expected is not None and abs(actual - expected) <= TOL_CHI2


def build_payload(run_official: bool = False) -> dict:
    rows = generate_camb_gr_rows(CosmologyPoint())
    write_spectra(BASELINE_PATH, rows)
    _write_candidate(rows, FROZEN_LAMBDA_T, FROZEN_LAMBDA_E, CANDIDATE_PATH)
    baseline = _run_likelihood_set(BASELINE_PATH, run_official)
    candidate = _run_likelihood_set(CANDIDATE_PATH, run_official)
    channels = (
        "highl_TT",
        "highl_TE",
        "highl_EE",
        "highl_TTTEEE",
        "lowl_TT",
        "lowl_EE",
        "lensing",
    )
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
    previous = accounting_payload()
    expected = {
        "highl_TT": previous.get("delta_chi2_highl_TT"),
        "highl_TE": previous.get("delta_chi2_highl_TE"),
        "highl_EE": previous.get("delta_chi2_highl_EE"),
        "highl_TTTEEE": previous.get("delta_chi2_highl_TTTEEE"),
        "combined": previous.get("nonoverlapping_total_combined_highl"),
        "decomposed": previous.get("nonoverlapping_total_decomposed_highl"),
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
        "status": "janus-z4-regenerative-frozen-candidate-replay-gate",
        "run_official_requested": run_official,
        "baseline_spectra_path": str(BASELINE_PATH),
        "candidate_spectra_path": str(CANDIDATE_PATH),
        "baseline_manifest": provenance_manifest(cosmology=CosmologyPoint(), lambda_T=0.0, lambda_E=0.0),
        "candidate_manifest": provenance_manifest(
            cosmology=CosmologyPoint(),
            lambda_T=FROZEN_LAMBDA_T,
            lambda_E=FROZEN_LAMBDA_E,
            z4_delta_source="reference_cosmology_replay",
        ),
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "z4_delta_source": "reference_cosmology_replay",
        "z4_deltas_regenerated_per_cosmology": False,
        "local_cosmology_profiling_allowed": False,
        "baseline": baseline,
        "candidate": candidate,
        "delta_chi2_by_channel": deltas,
        "nonoverlapping_total_combined_highl": combined,
        "nonoverlapping_total_decomposed_highl": decomposed,
        "expected_checkpoint_values": expected,
        "chi2_replay_tolerance": TOL_CHI2,
        "checkpoint_replay_matches": replay_match,
        "regenerative_frozen_candidate_replay_passed": replay_match,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative Frozen Candidate Replay Gate",
        "",
        f"Replay passed: `{payload['regenerative_frozen_candidate_replay_passed']}`",
        f"z4_delta_source: `{payload['z4_delta_source']}`",
        f"Z4 deltas regenerated per cosmology: `{payload['z4_deltas_regenerated_per_cosmology']}`",
        f"Local cosmology profiling allowed: `{payload['local_cosmology_profiling_allowed']}`",
        f"Combined non-overlap: `{payload['nonoverlapping_total_combined_highl']}`",
        f"Decomposed non-overlap: `{payload['nonoverlapping_total_decomposed_highl']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
