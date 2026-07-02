from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_acoustic_calculator_component_spectra_gate import (
    build_payload as component_payload,
)
from scripts.build_p0_eft_janus_z4_master_highl_acoustic_failure_autopsy_gate import (
    _damping_tail,
    _peak_rows,
    _zero_rows,
    TT_PEAK_BANDS,
    EE_PEAK_BANDS,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_shape_phase_damping_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_shape_phase_damping_gate.json")


def _read(path: str) -> dict[str, np.ndarray]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    return {key: np.asarray([float(row[key]) for row in rows], dtype=float) for key in ("ell", "cl_tt", "cl_te", "cl_ee", "cl_pp")}


def build_payload() -> dict:
    component = component_payload()
    base = _read(component["baseline_spectra_path"])
    cand = _read(component["total_spectra_path"])
    ell = base["ell"]
    tt_peaks = _peak_rows(ell, base["cl_tt"], cand["cl_tt"], TT_PEAK_BANDS)
    ee_peaks = _peak_rows(ell, base["cl_ee"], cand["cl_ee"], EE_PEAK_BANDS)
    te_zeros = _zero_rows(ell, base["cl_te"], cand["cl_te"])
    damping = {channel: _damping_tail(ell, base[channel], cand[channel]) for channel in ("cl_tt", "cl_te", "cl_ee")}
    max_peak_shift = max(abs(row["peak_shift"] or 0) for row in (*tt_peaks, *ee_peaks))
    max_zero_shift = max(abs(row["zero_shift"] or 0.0) for row in te_zeros)
    max_height_delta = max(abs(row["height_delta_fraction"] or 0.0) for row in (*tt_peaks, *ee_peaks))
    phase_guard = max_peak_shift <= 80 and max_zero_shift <= 20
    damping_guard = all(row["rms"] is not None and row["rms"] <= 0.15 for row in damping.values())
    amplitude_guard = max_height_delta <= 0.25
    return {
        "status": "janus-z4-master-acoustic-calculator-shape-phase-damping-gate",
        "component_spectra_gate_passed": component["internal_diagnostic_spectra_generated"],
        "tt_peak_diagnostics": tt_peaks,
        "te_zero_diagnostics": te_zeros,
        "ee_peak_diagnostics": ee_peaks,
        "damping_tail_diagnostics": damping,
        "max_peak_shift": max_peak_shift,
        "max_te_zero_shift": max_zero_shift,
        "max_peak_height_delta_fraction": max_height_delta,
        "phase_guard_passed": phase_guard,
        "damping_guard_passed": damping_guard,
        "amplitude_guard_passed": amplitude_guard,
        "internal_shape_phase_damping_diagnostics_ready": True,
        "solver_shape_acceptable_for_internal_diagnostics": bool(phase_guard and damping_guard and amplitude_guard),
        "observed_likelihood_allowed": False,
        "planck_retry_allowed": False,
        "candidate_promotion_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterSolverProvenanceManifestGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Acoustic Calculator Shape Phase Damping Gate",
        "",
        f"Diagnostics ready: `{payload['internal_shape_phase_damping_diagnostics_ready']}`",
        f"Internal shape acceptable: `{payload['solver_shape_acceptable_for_internal_diagnostics']}`",
        f"Max peak shift: `{payload['max_peak_shift']}`",
        f"Max TE zero shift: `{payload['max_te_zero_shift']}`",
        f"Planck retry allowed: `{payload['planck_retry_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
