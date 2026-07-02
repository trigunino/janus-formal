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
from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_spectra_generation_gate import (
    build_payload as spectra_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_regularized_diagnostic_shape_report_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_regularized_diagnostic_shape_report_gate.json")


def _read(path: str) -> dict[str, np.ndarray]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    return {key: np.asarray([float(row[key]) for row in rows], dtype=float) for key in ("ell", *CHANNELS)}


def build_payload() -> dict:
    spectra = spectra_payload()
    base = _read(spectra["baseline_spectra_path"])
    cand = _read(spectra["candidate_spectra_path"])
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
    zero_artifacts = {
        channel: row["zero_count_delta"]
        for channel, row in rows.items()
        if row["zero_count_delta"] != 0
    }
    max_dev = max(row["max_abs_fractional_deviation"] for row in rows.values())
    max_peak_shift = max(abs(row["peak_shift"]) for row in rows.values())
    shape_lock_active = bool(zero_artifacts or max_dev > 1.0)
    return {
        "status": "janus-z4-master-regularized-diagnostic-shape-report-gate",
        "regularized_diagnostic_spectra_generation_gate_passed": spectra[
            "regularized_diagnostic_spectra_generated"
        ],
        "shape_rows": rows,
        "zero_crossing_artifacts": zero_artifacts,
        "max_abs_fractional_deviation": max_dev,
        "max_abs_peak_shift": max_peak_shift,
        "regularized_shape_report_generated": True,
        "phase_guard_passed": max_peak_shift <= 200,
        "amplitude_guard_passed": max_dev <= 1.0,
        "pre_likelihood_shape_lock_active": shape_lock_active,
        "diagnostic_only": True,
        "full_upstream_action_derived": False,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterActionNormalizationGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Regularized Diagnostic Shape Report Gate",
        "",
        f"Shape lock active: `{payload['pre_likelihood_shape_lock_active']}`",
        f"Zero artifacts: `{payload['zero_crossing_artifacts']}`",
        f"Max abs fractional deviation: `{payload['max_abs_fractional_deviation']}`",
        f"Full upstream action derived: `{payload['full_upstream_action_derived']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
