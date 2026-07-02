from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_observed_failure_map_v2_gate import (
    build_payload as failure_v2_payload,
)
from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_spectra_v2_gate import (
    build_payload as spectra_v2_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_highl_acoustic_failure_autopsy_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_highl_acoustic_failure_autopsy_gate.json")
FAILURE_JSON = Path("outputs/reports/p0_eft_janus_z4_master_observed_failure_map_v2_gate.json")
SPECTRA_JSON = Path("outputs/reports/p0_eft_janus_z4_master_regularized_diagnostic_spectra_v2_gate.json")

CHANNELS = ("cl_tt", "cl_te", "cl_ee")
TT_PEAK_BANDS = ((150, 350), (400, 650), (650, 950))
EE_PEAK_BANDS = ((250, 550), (550, 850), (850, 1250))
TE_ZERO_BANDS = ((150, 400), (400, 750), (750, 1150))


def _load_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None


def _read(path: str) -> dict[str, np.ndarray]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    return {key: np.asarray([float(row[key]) for row in rows], dtype=float) for key in ("ell", "cl_tt", "cl_te", "cl_ee", "cl_pp")}


def _band_mask(ell: np.ndarray, band: tuple[int, int]) -> np.ndarray:
    return (ell >= band[0]) & (ell <= band[1])


def _peak_in_band(ell: np.ndarray, values: np.ndarray, band: tuple[int, int], use_abs: bool = False) -> dict:
    mask = _band_mask(ell, band)
    if not np.any(mask):
        return {"ell": None, "height": None}
    local_ell = ell[mask]
    local_values = values[mask]
    target = np.abs(local_values) if use_abs else local_values
    idx = int(np.argmax(target))
    return {"ell": int(local_ell[idx]), "height": float(local_values[idx])}


def _peak_rows(ell: np.ndarray, base: np.ndarray, cand: np.ndarray, bands: tuple[tuple[int, int], ...], use_abs: bool = False) -> list[dict]:
    rows = []
    for band in bands:
        base_peak = _peak_in_band(ell, base, band, use_abs=use_abs)
        cand_peak = _peak_in_band(ell, cand, band, use_abs=use_abs)
        base_height = base_peak["height"]
        cand_height = cand_peak["height"]
        height_delta_fraction = None
        if base_height is not None and abs(base_height) > 1.0e-30:
            height_delta_fraction = float(cand_height / base_height - 1.0)
        rows.append(
            {
                "band": list(band),
                "baseline_peak_ell": base_peak["ell"],
                "candidate_peak_ell": cand_peak["ell"],
                "peak_shift": None
                if base_peak["ell"] is None or cand_peak["ell"] is None
                else int(cand_peak["ell"] - base_peak["ell"]),
                "baseline_height": base_height,
                "candidate_height": cand_height,
                "height_delta_fraction": height_delta_fraction,
            }
        )
    return rows


def _zero_crossing_in_band(ell: np.ndarray, values: np.ndarray, band: tuple[int, int]) -> float | None:
    mask = _band_mask(ell, band)
    local_ell = ell[mask]
    local_values = values[mask]
    if len(local_ell) < 2:
        return None
    signs = np.sign(local_values)
    crossings = np.where(signs[:-1] * signs[1:] < 0.0)[0]
    if len(crossings) == 0:
        return None
    idx = int(crossings[0])
    x0, x1 = float(local_ell[idx]), float(local_ell[idx + 1])
    y0, y1 = float(local_values[idx]), float(local_values[idx + 1])
    return x0 - y0 * (x1 - x0) / (y1 - y0)


def _zero_rows(ell: np.ndarray, base: np.ndarray, cand: np.ndarray) -> list[dict]:
    rows = []
    for band in TE_ZERO_BANDS:
        base_zero = _zero_crossing_in_band(ell, base, band)
        cand_zero = _zero_crossing_in_band(ell, cand, band)
        rows.append(
            {
                "band": list(band),
                "baseline_zero_ell": base_zero,
                "candidate_zero_ell": cand_zero,
                "zero_shift": None if base_zero is None or cand_zero is None else float(cand_zero - base_zero),
                "sign_error": bool((base_zero is None) != (cand_zero is None)),
            }
        )
    return rows


def _fractional_residual(ell: np.ndarray, base: np.ndarray, cand: np.ndarray, band: tuple[int, int]) -> np.ndarray:
    mask = _band_mask(ell, band) & (np.abs(base) > 1.0e-30)
    return cand[mask] / base[mask] - 1.0


def _damping_tail(ell: np.ndarray, base: np.ndarray, cand: np.ndarray) -> dict:
    band = (1200, 2500)
    mask = _band_mask(ell, band) & (np.abs(base) > 1.0e-30)
    if int(np.sum(mask)) < 2:
        return {"band": list(band), "rms": None, "slope_per_ell": None, "trend": "insufficient_data"}
    x = ell[mask].astype(float)
    frac = cand[mask] / base[mask] - 1.0
    slope = float(np.polyfit(x, frac, 1)[0])
    rms = float(np.sqrt(np.mean(np.square(frac))))
    trend = "rising" if slope > 1.0e-5 else "falling" if slope < -1.0e-5 else "flat"
    return {"band": list(band), "rms": rms, "slope_per_ell": slope, "trend": trend}


def _rms_by_channel(ell: np.ndarray, base: dict[str, np.ndarray], cand: dict[str, np.ndarray]) -> dict:
    out = {}
    for channel in CHANNELS:
        frac = _fractional_residual(ell, base[channel], cand[channel], (30, 2500))
        out[channel] = float(np.sqrt(np.mean(np.square(frac)))) if len(frac) else None
    return out


def build_payload() -> dict:
    failure = _load_json(FAILURE_JSON) or failure_v2_payload()
    spectra = _load_json(SPECTRA_JSON) or spectra_v2_payload()
    base = _read(spectra["baseline_spectra_path"])
    cand = _read(spectra["candidate_spectra_path"])
    ell = base["ell"]
    tt_peaks = _peak_rows(ell, base["cl_tt"], cand["cl_tt"], TT_PEAK_BANDS)
    ee_peaks = _peak_rows(ell, base["cl_ee"], cand["cl_ee"], EE_PEAK_BANDS)
    te_zeros = _zero_rows(ell, base["cl_te"], cand["cl_te"])
    damping = {
        channel: _damping_tail(ell, base[channel], cand[channel])
        for channel in CHANNELS
    }
    rms = _rms_by_channel(ell, base, cand)
    max_peak_shift = max(abs(row["peak_shift"] or 0) for row in (*tt_peaks, *ee_peaks))
    max_zero_shift = max(abs(row["zero_shift"] or 0.0) for row in te_zeros)
    max_height_delta = max(
        abs(row["height_delta_fraction"] or 0.0)
        for row in (*tt_peaks, *ee_peaks)
    )
    damping_tail_failure = any(
        row["rms"] is not None and row["rms"] > 0.05 for row in damping.values()
    )
    phase_failure = bool(max_peak_shift > 30 or max_zero_shift > 30)
    height_failure = bool(max_height_delta > 0.05)
    if phase_failure:
        subclass = "acoustic_phase_failure"
    elif damping_tail_failure:
        subclass = "damping_tail_or_high_l_shape_failure"
    elif height_failure:
        subclass = "acoustic_driving_or_baryon_loading_failure"
    else:
        subclass = "likelihood_weighted_high_l_failure"
    return {
        "status": "janus-z4-master-highl-acoustic-failure-autopsy-gate",
        "observed_failure_map_v2_rejected": failure["observed_master_v2_branch_rejected"],
        "observed_failure_class": failure["failure_class"],
        "dominant_observed_channel": failure["dominant_failure_channel"],
        "nonoverlapping_total_combined_highl": failure["nonoverlapping_total_combined_highl"],
        "nonoverlapping_total_decomposed_highl": failure["nonoverlapping_total_decomposed_highl"],
        "tt_peak_diagnostics": tt_peaks,
        "te_zero_diagnostics": te_zeros,
        "ee_peak_diagnostics": ee_peaks,
        "damping_tail_diagnostics": damping,
        "highl_fractional_rms": rms,
        "max_peak_shift": max_peak_shift,
        "max_te_zero_shift": max_zero_shift,
        "max_peak_height_delta_fraction": max_height_delta,
        "phase_failure": phase_failure,
        "height_failure": height_failure,
        "damping_tail_failure": damping_tail_failure,
        "failure_subclass": subclass,
        "unlensed_lensed_split_available": False,
        "unlensed_lensed_split_reason": "diagnostic spectra are lensed total Cl only",
        "source_component_attribution": {
            "surface_SW": "requires source-component spectra",
            "early_ISW": "requires source-component spectra",
            "Doppler": "requires source-component spectra",
            "polarization_Pi": "requires source-component spectra",
        },
        "source_component_attribution_complete": False,
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "new_physics_allowed": False,
        "retuning_allowed": False,
        "planck_retry_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterPhotonBaryonMatchingGate_or_archive_master_v2_mapping",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master High-L Acoustic Failure Autopsy Gate",
        "",
        f"Observed failure class: `{payload['observed_failure_class']}`",
        f"Failure subclass: `{payload['failure_subclass']}`",
        f"Dominant observed channel: `{payload['dominant_observed_channel']}`",
        f"Combined non-overlap: `{payload['nonoverlapping_total_combined_highl']}`",
        f"Decomposed non-overlap: `{payload['nonoverlapping_total_decomposed_highl']}`",
        f"Max peak shift: `{payload['max_peak_shift']}`",
        f"Max TE zero shift: `{payload['max_te_zero_shift']}`",
        f"Max peak height delta fraction: `{payload['max_peak_height_delta_fraction']}`",
        f"Damping tail failure: `{payload['damping_tail_failure']}`",
        f"Unlensed/lensed split available: `{payload['unlensed_lensed_split_available']}`",
        f"Retuning allowed: `{payload['retuning_allowed']}`",
        f"New physics allowed: `{payload['new_physics_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
