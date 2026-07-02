from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_diagnostic_shape_report_gate import (
    CHANNELS,
    _peak_ell,
    _ratio_stats,
    _zero_count,
)
from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_spectra_v2_gate import (
    build_payload as spectra_v2_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_shape_report_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_shape_report_v2_gate.json")


def _read(path: str) -> dict[str, np.ndarray]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    return {key: np.asarray([float(row[key]) for row in rows], dtype=float) for key in ("ell", *CHANNELS)}


def _fractional_rms(base: np.ndarray, cand: np.ndarray) -> float:
    mask = np.abs(base) > 1.0e-30
    frac = cand[mask] / base[mask] - 1.0
    return float(np.sqrt(np.mean(np.square(frac))))


def build_payload() -> dict:
    spectra = spectra_v2_payload()
    base = _read(spectra["baseline_spectra_path"])
    cand = _read(spectra["candidate_spectra_path"])
    rows = {}
    decomposed_terms = {}
    for channel in CHANNELS:
        rows[channel] = {
            **_ratio_stats(base[channel], cand[channel]),
            "baseline_peak_ell": _peak_ell(base["ell"], base[channel]),
            "candidate_peak_ell": _peak_ell(cand["ell"], cand[channel]),
            "peak_shift": _peak_ell(cand["ell"], cand[channel]) - _peak_ell(base["ell"], base[channel]),
            "baseline_zero_count": _zero_count(base[channel]),
            "candidate_zero_count": _zero_count(cand[channel]),
            "zero_count_delta": _zero_count(cand[channel]) - _zero_count(base[channel]),
        }
        decomposed_terms[channel] = _fractional_rms(base[channel], cand[channel])

    all_frac = []
    for channel in CHANNELS:
        mask = np.abs(base[channel]) > 1.0e-30
        all_frac.append(cand[channel][mask] / base[channel][mask] - 1.0)
    combined_highl_shape_norm = float(np.sqrt(np.mean(np.square(np.concatenate(all_frac)))))
    decomposed_highl_shape_norm = float(sum(decomposed_terms.values()))
    max_dev = max(row["max_abs_fractional_deviation"] for row in rows.values())
    max_peak_shift = max(abs(row["peak_shift"]) for row in rows.values())
    zero_artifacts = {channel: row["zero_count_delta"] for channel, row in rows.items() if row["zero_count_delta"] != 0}
    return {
        "status": "janus-z4-master-diagnostic-shape-report-v2-gate",
        "diagnostic_spectra_v2_gate_passed": spectra["diagnostic_spectra_v2_generated"],
        "shape_rows": rows,
        "max_abs_fractional_deviation": max_dev,
        "max_abs_peak_shift": max_peak_shift,
        "zero_crossing_artifacts": zero_artifacts,
        "shape_report_v2_generated": True,
        "phase_guard_passed": max_peak_shift <= 200,
        "amplitude_guard_passed": max_dev <= 1.0,
        "zero_artifact_guard_passed": not zero_artifacts,
        "nonoverlap_accounting_basis_declared": True,
        "combined_highl_shape_norm": combined_highl_shape_norm,
        "decomposed_highl_shape_norm": decomposed_highl_shape_norm,
        "overlapping_sum_forbidden": True,
        "reported_total_uses_one_highl_basis_only": True,
        "diagnostic_only": True,
        "likelihood_evaluation_allowed": False,
        "official_planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterPreLikelihoodLockV2Gate"
        if max_peak_shift <= 200 and max_dev <= 1.0 and not zero_artifacts
        else "revise_master_v2_shape",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Diagnostic Shape Report V2 Gate",
        "",
        f"Shape report generated: `{payload['shape_report_v2_generated']}`",
        f"Max abs fractional deviation: `{payload['max_abs_fractional_deviation']}`",
        f"Max abs peak shift: `{payload['max_abs_peak_shift']}`",
        f"Zero artifact guard: `{payload['zero_artifact_guard_passed']}`",
        f"Combined high-l shape norm: `{payload['combined_highl_shape_norm']}`",
        f"Decomposed high-l shape norm: `{payload['decomposed_highl_shape_norm']}`",
        f"Likelihood allowed: `{payload['likelihood_evaluation_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
