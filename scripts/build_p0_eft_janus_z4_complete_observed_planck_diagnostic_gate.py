from __future__ import annotations

import csv
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
    sys.path.insert(0, str(ROOT / "src"))

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, default_ell_grid, generate_camb_gr_rows, write_spectra
from scripts.build_p0_eft_janus_z4_complete_cl_convention_calibration_gate import (
    CALIBRATED_VECTOR_PATH,
    build_payload as calibration_payload,
)
from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import LIKELIHOODS, _run_likelihood

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_observed_planck_diagnostic_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_observed_planck_diagnostic_gate.json")
SPECTRA_DIR = Path("outputs/reports/z4_complete_observed_planck_diagnostic")
BASELINE_CSV = SPECTRA_DIR / "complete_gr_baseline.csv"
CANDIDATE_CSV = SPECTRA_DIR / "complete_z4_candidate_calibrated.csv"
CHANNELS = ("highl_TT", "highl_TE", "highl_EE", "highl_TTTEEE", "lowl_TT", "lowl_EE", "lensing")


def _tail_extrapolate(x: np.ndarray, y: np.ndarray, target: np.ndarray) -> np.ndarray:
    values = np.interp(target, x, y)
    mask = target > x[-1]
    if not np.any(mask):
        return values
    y0, y1 = float(y[-2]), float(y[-1])
    if y0 == 0.0 or y1 == 0.0 or math.copysign(1.0, y0) != math.copysign(1.0, y1):
        values[mask] = y1
        return values
    power = math.log(abs(y1 / y0)) / math.log(float(x[-1] / x[-2]))
    values[mask] = math.copysign(abs(y1), y1) * np.power(target[mask] / x[-1], power)
    return values


def _candidate_rows(vector: dict, ells: list[int]) -> list[dict[str, float]]:
    source_ell = np.asarray(vector["ell"], dtype=float)
    target = np.asarray(ells, dtype=float)
    channels = {
        "cl_tt": _tail_extrapolate(source_ell, np.asarray(vector["cl_tt"], dtype=float), target),
        "cl_te": _tail_extrapolate(source_ell, np.asarray(vector["cl_te"], dtype=float), target),
        "cl_ee": _tail_extrapolate(source_ell, np.asarray(vector["cl_ee"], dtype=float), target),
        "cl_pp": _tail_extrapolate(source_ell, np.asarray(vector["cl_phiphi"], dtype=float), target),
    }
    return [
        {
            "ell": int(ell),
            "cl_tt": float(channels["cl_tt"][idx]),
            "cl_te": float(channels["cl_te"][idx]),
            "cl_ee": float(channels["cl_ee"][idx]),
            "cl_pp": float(channels["cl_pp"][idx]),
        }
        for idx, ell in enumerate(ells)
    ]


def write_spectra_inputs() -> dict:
    calibration = calibration_payload()
    vector = json.loads(CALIBRATED_VECTOR_PATH.read_text(encoding="utf-8"))
    ells = default_ell_grid()
    baseline_rows = generate_camb_gr_rows(CosmologyPoint(), ells=ells)
    candidate_rows = _candidate_rows(vector, ells)
    write_spectra(BASELINE_CSV, baseline_rows)
    write_spectra(CANDIDATE_CSV, candidate_rows)
    return {
        "calibration_passed": calibration["cl_convention_calibration_passed"],
        "baseline_spectra_path": str(BASELINE_CSV),
        "candidate_spectra_path": str(CANDIDATE_CSV),
        "ell_min": min(ells),
        "ell_max": max(ells),
        "ell_count": len(ells),
        "candidate_extension_policy": "log_power_tail_to_ell_2508",
    }


def _evaluate(path: Path, run_observed: bool) -> dict:
    if not run_observed:
        return {"channels": {}, "finite_channel_chi2": {}, "total_finite_chi2": None}
    channels = {name: _run_likelihood(component, path) for name, component in LIKELIHOODS.items()}
    finite = {name: row["chi2"] for name, row in channels.items() if row["finite"]}
    return {
        "channels": channels,
        "finite_channel_chi2": finite,
        "total_finite_chi2": float(sum(finite.values())) if finite else None,
    }


def _delta(candidate: dict, baseline: dict, channel: str) -> float | None:
    c = candidate.get("finite_channel_chi2", {}).get(channel)
    b = baseline.get("finite_channel_chi2", {}).get(channel)
    return float(c - b) if c is not None and b is not None else None


def build_payload(run_observed: bool = False) -> dict:
    spectra = write_spectra_inputs()
    execute = bool(run_observed and spectra["calibration_passed"] and spectra["ell_max"] >= 2508)
    baseline = _evaluate(BASELINE_CSV, execute)
    candidate = _evaluate(CANDIDATE_CSV, execute)
    deltas = {channel: _delta(candidate, baseline, channel) for channel in CHANNELS}
    finite = [value for value in deltas.values() if value is not None]
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
    available_combined = (
        deltas["highl_TTTEEE"] + deltas["lensing"]
        if all(deltas[k] is not None for k in ("highl_TTTEEE", "lensing"))
        else None
    )
    available_decomposed = (
        deltas["highl_TT"] + deltas["highl_TE"] + deltas["highl_EE"] + deltas["lensing"]
        if all(deltas[k] is not None for k in ("highl_TT", "highl_TE", "highl_EE", "lensing"))
        else None
    )
    low_l_nonfinite = bool(execute and (deltas["lowl_TT"] is None or deltas["lowl_EE"] is None))
    clean = bool(execute and combined is not None and decomposed is not None and combined < 0.0 and decomposed < 0.0)
    return {
        "status": "janus-z4-complete-observed-planck-diagnostic-gate",
        **spectra,
        "run_observed_requested": run_observed,
        "run_observed_executed": execute,
        "baseline": baseline,
        "candidate": candidate,
        "delta_chi2_by_channel": deltas,
        "legacy_overlapping_total": float(sum(finite)) if len(finite) == len(CHANNELS) else None,
        "nonoverlapping_total_combined_highl": combined,
        "nonoverlapping_total_decomposed_highl": decomposed,
        "available_nonoverlap_highl_lensing_combined": available_combined,
        "available_nonoverlap_highl_lensing_decomposed": available_decomposed,
        "low_l_rejected_or_nonfinite": low_l_nonfinite,
        "nonoverlap_accounting_required": True,
        "clean_nonoverlap_result": clean,
        "diagnostic_trial_passed": bool(execute and clean),
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4CompleteObservedNonOverlapAccountingGate"
        if execute
        else "run_with_observed_planck_explicitly_if_requested",
    }


def write_reports(run_observed: bool = False) -> dict:
    payload = build_payload(run_observed=run_observed)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete Observed Planck Diagnostic Gate",
            "",
            f"Observed run executed: `{payload['run_observed_executed']}`",
            f"Combined non-overlap: `{payload['nonoverlapping_total_combined_highl']}`",
            f"Decomposed non-overlap: `{payload['nonoverlapping_total_decomposed_highl']}`",
            f"Full Planck validation: `{payload['full_planck_validation']}`",
            f"Next gate: `{payload['next_required_gate']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_observed=False), indent=2))
