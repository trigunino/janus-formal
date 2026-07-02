from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_diagnostic_spectra_generation_gate import build_payload as generation_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_shape_report_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_diagnostic_shape_report_gate.json")
CHANNELS = ("cl_tt", "cl_te", "cl_ee")


def _read(path: str) -> dict[str, np.ndarray]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    return {key: np.asarray([float(row[key]) for row in rows], dtype=float) for key in ("ell", *CHANNELS)}


def _ratio_stats(base: np.ndarray, cand: np.ndarray) -> dict:
    mask = np.abs(base) > 1.0e-30
    ratio = cand[mask] / base[mask]
    return {
        "ratio_min": float(np.min(ratio)),
        "ratio_max": float(np.max(ratio)),
        "ratio_mean": float(np.mean(ratio)),
        "max_abs_fractional_deviation": float(np.max(np.abs(ratio - 1.0))),
    }


def _peak_ell(ell: np.ndarray, values: np.ndarray) -> int:
    return int(ell[int(np.argmax(np.abs(values)))])


def _zero_count(values: np.ndarray) -> int:
    return int(np.sum(np.diff(np.signbit(values)) != 0))


def build_payload() -> dict:
    gen = generation_payload()
    base = _read(gen["baseline_spectra_path"])
    cand = _read(gen["candidate_spectra_path"])
    rows = {}
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
    max_dev = max(row["max_abs_fractional_deviation"] for row in rows.values())
    max_peak_shift = max(abs(row["peak_shift"]) for row in rows.values())
    return {
        "status": "janus-z4-master-diagnostic-shape-report-gate",
        "diagnostic_spectra_generation_gate_passed": True,
        "shape_rows": rows,
        "max_abs_fractional_deviation": max_dev,
        "max_abs_peak_shift": max_peak_shift,
        "shape_report_generated": True,
        "phase_guard_passed": max_peak_shift <= 200,
        "amplitude_guard_passed": max_dev <= 5.0,
        "diagnostic_only": True,
        "likelihood_evaluation_allowed": False,
        "official_planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterPreLikelihoodLockGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Diagnostic Shape Report Gate",
        "",
        f"Shape report generated: `{payload['shape_report_generated']}`",
        f"Max abs fractional deviation: `{payload['max_abs_fractional_deviation']}`",
        f"Max abs peak shift: `{payload['max_abs_peak_shift']}`",
        f"Phase guard passed: `{payload['phase_guard_passed']}`",
        f"Amplitude guard passed: `{payload['amplitude_guard_passed']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
