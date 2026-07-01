from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_weyl_lensing_delta_gate import (
    _apply_lensing_delta,
    _baseline_spectra,
    _load_baseline,
    build_payload as weyl_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_lensed_remapping_response_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_lensed_remapping_response_gate.json")


def _smooth(values: np.ndarray, strength: np.ndarray) -> np.ndarray:
    kernel = np.array([0.06, 0.24, 0.40, 0.24, 0.06])
    padded = np.pad(values, (2, 2), mode="edge")
    local = np.convolve(padded, kernel, mode="valid")
    return (1.0 - strength) * values + strength * local


def _lensed_from_phiphi(ell: np.ndarray, unlensed: dict[str, np.ndarray], phiphi: np.ndarray) -> dict[str, np.ndarray]:
    pp = np.maximum(phiphi, 0.0)
    norm = np.nanmax(pp[8:]) if len(pp) > 8 else np.nanmax(pp)
    strength = np.clip(np.sqrt(pp / max(float(norm), 1.0e-300)) * 0.018, 0.0, 0.018)
    strength = strength * np.clip(ell / 1200.0, 0.0, 1.0)
    return {
        "tt": _smooth(unlensed["tt"], strength),
        "te": _smooth(unlensed["te"], strength),
        "ee": _smooth(unlensed["ee"], strength),
        "pp": phiphi.copy(),
    }


def _max_frac_delta(a: np.ndarray, b: np.ndarray) -> float:
    scale = max(float(np.nanmax(np.abs(a))), 1.0e-300)
    return float(np.nanmax(np.abs(b - a)) / scale)


def _peak(values: np.ndarray, ell: np.ndarray, low: float, high: float) -> int:
    mask = (ell >= low) & (ell <= high) & np.isfinite(values)
    return int(ell[mask][np.argmax(values[mask])])


def _zeros(values: np.ndarray, ell: np.ndarray) -> list[int]:
    mask = (ell >= 30.0) & (ell <= 1200.0) & np.isfinite(values)
    e = ell[mask].astype(int)
    v = values[mask]
    out: list[int] = []
    for idx in range(len(v) - 1):
        if v[idx] == 0.0 or v[idx] * v[idx + 1] < 0.0:
            out.append(int(e[idx]))
    return out[:8]


def _band_rms_delta(ell: np.ndarray, base: np.ndarray, values: np.ndarray, low: float, high: float) -> float:
    mask = (ell >= low) & (ell <= high)
    denom = np.maximum(np.abs(base[mask]), np.nanmax(np.abs(base[mask])) * 1.0e-12)
    return float(np.sqrt(np.nanmean(np.square((values[mask] - base[mask]) / denom))))


def _response_for_lambda(
    ell: np.ndarray,
    unlensed: dict[str, np.ndarray],
    response: float,
    lambda_z4: float,
) -> dict:
    z4 = _apply_lensing_delta(unlensed, response, lambda_z4)
    gr_lensed = _lensed_from_phiphi(ell, unlensed, unlensed["pp"])
    z4_lensed = _lensed_from_phiphi(ell, unlensed, z4["pp"])
    unlensed_delta = {
        channel: _max_frac_delta(unlensed[channel], z4[channel])
        for channel in ("tt", "te", "ee")
    }
    lensed_delta = {
        channel: _max_frac_delta(gr_lensed[channel], z4_lensed[channel])
        for channel in ("tt", "te", "ee")
    }
    te_zeros_gr = _zeros(gr_lensed["te"], ell)
    te_zeros_z4 = _zeros(z4_lensed["te"], ell)
    te_zero_shift = max(
        [abs(a - b) for a, b in zip(te_zeros_gr, te_zeros_z4)] or [0]
    )
    return {
        "lambda_z4": lambda_z4,
        "finite": all(np.isfinite(z4_lensed[channel]).all() for channel in z4_lensed),
        "unlensed_primary_delta": unlensed_delta,
        "unlensed_primary_unchanged": max(unlensed_delta.values()) < 1.0e-14,
        "phiphi_response": _max_frac_delta(unlensed["pp"], z4["pp"]),
        "lensed_response": lensed_delta,
        "lensed_TT_response_rms_acoustic": _band_rms_delta(ell, gr_lensed["tt"], z4_lensed["tt"], 30.0, 1200.0),
        "lensed_TE_response_rms_acoustic": _band_rms_delta(ell, gr_lensed["te"], z4_lensed["te"], 30.0, 1200.0),
        "lensed_EE_response_rms_acoustic": _band_rms_delta(ell, gr_lensed["ee"], z4_lensed["ee"], 30.0, 1200.0),
        "TT_first_peak_shift": _peak(z4_lensed["tt"], ell, 30.0, 450.0) - _peak(gr_lensed["tt"], ell, 30.0, 450.0),
        "EE_first_peak_shift": _peak(z4_lensed["ee"], ell, 30.0, 450.0) - _peak(gr_lensed["ee"], ell, 30.0, 450.0),
        "TE_zero_shift_max": te_zero_shift,
        "TE_zero_crossings_GR": te_zeros_gr,
        "TE_zero_crossings_Z4": te_zeros_z4,
        "positive_auto_spectra": bool(
            np.nanmin(z4_lensed["tt"][ell >= 2.0]) >= 0.0
            and np.nanmin(z4_lensed["ee"][ell >= 2.0]) >= 0.0
            and np.nanmin(z4_lensed["pp"][ell >= 2.0]) >= 0.0
        ),
    }


def build_payload() -> dict:
    rows = _load_baseline()
    ell, unlensed = _baseline_spectra(rows)
    weyl = weyl_payload()
    response = float(weyl["kernel"]["kernel_response_dCphiphi_over_Cphiphi_per_lambda"])
    lambdas = [0.0, 1.0e-6, 1.0e-4, 1.0e-3, 1.0]
    responses = {str(lam): _response_for_lambda(ell, unlensed, response, lam) for lam in lambdas}
    zero = responses["0.0"]
    small = [responses[str(lam)] for lam in (1.0e-6, 1.0e-4, 1.0e-3)]
    identity = bool(
        zero["finite"]
        and zero["unlensed_primary_unchanged"]
        and zero["phiphi_response"] == 0.0
        and max(zero["lensed_response"].values()) < 1.0e-14
    )
    continuity = all(
        row["finite"]
        and row["positive_auto_spectra"]
        and row["unlensed_primary_unchanged"]
        and row["TT_first_peak_shift"] == 0
        and row["EE_first_peak_shift"] == 0
        and row["TE_zero_shift_max"] == 0
        for row in small
    )
    return {
        "status": "janus-z4-lensed-remapping-response-gate",
        "input_unlensed_backend": "camb_gr_safe_baseline",
        "input_phiphi_delta": "weyl_lensing_kernel",
        "raw_native_los_used_for_planck": False,
        "allowed_to_modify_unlensed_primary": False,
        "allowed_to_modify_phiphi": True,
        "allowed_to_modify_lensed_spectra": True,
        "lambda_zero_identity_passed": identity,
        "responses": responses,
        "lensed_TT_response_continuous": continuity,
        "lensed_TE_response_continuous": continuity,
        "lensed_EE_response_continuous": continuity,
        "TT_peak_positions_unchanged_or_smooth": continuity,
        "TE_zero_crossings_not_jumped": continuity,
        "EE_peak_positions_not_jumped": continuity,
        "lensed_remapping_response_gate_passed": bool(identity and continuity and weyl["internal_lensing_response_gate_passed"]),
        "uniform_phiphi_amplitude_delta_screened_by_normalized_smoothing": bool(responses["1.0"]["phiphi_response"] > 0.0 and max(responses["1.0"]["lensed_response"].values()) < 1.0e-12),
        "observable_lensing_shape_delta_required": bool(max(responses["1.0"]["lensed_response"].values()) < 1.0e-12),
        "nonzero_z4_planck_allowed": False,
        "official_planck_allowed": False,
        "next_required_action": "add nonzero-Z4 Planck eligibility gate or derive SW/ISW delta after remapping remains stable",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    one = payload["responses"]["1.0"]
    lines = [
        "# Janus Z4 Lensed Remapping Response Gate",
        "",
        f"lambda=0 identity: `{payload['lambda_zero_identity_passed']}`",
        f"Lensed remapping response gate passed: `{payload['lensed_remapping_response_gate_passed']}`",
        f"Nonzero Z4 Planck allowed: `{payload['nonzero_z4_planck_allowed']}`",
        "",
        "## Lambda=1 Response",
        f"- phiphi response: `{one['phiphi_response']}`",
        f"- TT lensed max response: `{one['lensed_response']['tt']}`",
        f"- TE lensed max response: `{one['lensed_response']['te']}`",
        f"- EE lensed max response: `{one['lensed_response']['ee']}`",
        f"- TT peak shift: `{one['TT_first_peak_shift']}`",
        f"- TE zero max shift: `{one['TE_zero_shift_max']}`",
        f"- EE peak shift: `{one['EE_first_peak_shift']}`",
        f"- uniform phiphi amplitude screened: `{payload['uniform_phiphi_amplitude_delta_screened_by_normalized_smoothing']}`",
        f"- observable lensing shape delta required: `{payload['observable_lensing_shape_delta_required']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
