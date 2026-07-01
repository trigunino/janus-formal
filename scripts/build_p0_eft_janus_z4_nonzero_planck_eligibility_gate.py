from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_controlled_deviation_gate import build_payload as controlled_payload
from scripts.build_p0_eft_janus_z4_gr_baseline_reduction_gate import build_payload as baseline_payload
from scripts.build_p0_eft_janus_z4_lensed_remapping_response_gate import _lensed_from_phiphi
from scripts.build_p0_eft_janus_z4_lensing_shape_delta_gate import (
    _apply_shape_delta,
    _baseline,
    _load_baseline,
    _shape_kernel_response,
    build_payload as shape_payload,
)
from scripts.build_p0_eft_janus_z4_weyl_lensing_delta_gate import build_payload as weyl_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_nonzero_planck_eligibility_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_nonzero_planck_eligibility_gate.json")

SMALL_LAMBDAS = (0.0, 1.0e-8, 1.0e-6, 1.0e-4, 1.0e-3, 1.0e-2)


def _max_rel(a: np.ndarray, b: np.ndarray) -> float:
    scale = max(float(np.nanmax(np.abs(a))), 1.0e-300)
    return float(np.nanmax(np.abs(b - a)) / scale)


def _zeros(values: np.ndarray, ell: np.ndarray) -> list[int]:
    mask = (ell >= 30.0) & (ell <= 1200.0) & np.isfinite(values)
    e = ell[mask].astype(int)
    v = values[mask]
    out: list[int] = []
    for idx in range(len(v) - 1):
        if v[idx] == 0.0 or v[idx] * v[idx + 1] < 0.0:
            out.append(int(e[idx]))
    return out[:8]


def _peak(values: np.ndarray, ell: np.ndarray, low: float, high: float) -> int:
    mask = (ell >= low) & (ell <= high) & np.isfinite(values)
    return int(ell[mask][np.argmax(values[mask])])


def _spectral_checks() -> dict:
    ell, base = _baseline(_load_baseline())
    q_l = _shape_kernel_response(ell)
    gr_lensed = _lensed_from_phiphi(ell, base, base["pp"])
    zero = _apply_shape_delta(base, q_l, 0.0)
    zero_lensed = _lensed_from_phiphi(ell, base, zero["pp"])
    lambda_zero_errors = {
        "TT": _max_rel(base["tt"], zero["tt"]),
        "TE": _max_rel(base["te"], zero["te"]),
        "EE": _max_rel(base["ee"], zero["ee"]),
        "phiphi": _max_rel(base["pp"], zero["pp"]),
        "lensed_TT": _max_rel(gr_lensed["tt"], zero_lensed["tt"]),
        "lensed_TE": _max_rel(gr_lensed["te"], zero_lensed["te"]),
        "lensed_EE": _max_rel(gr_lensed["ee"], zero_lensed["ee"]),
    }
    lambda_zero_identity = all(value < 1.0e-14 for value in lambda_zero_errors.values())
    gr_te_zeros = _zeros(gr_lensed["te"], ell)
    continuity = {}
    for lam in SMALL_LAMBDAS:
        z4 = _apply_shape_delta(base, q_l, lam)
        z4_lensed = _lensed_from_phiphi(ell, base, z4["pp"])
        primary_delta = {channel: _max_rel(base[channel], z4[channel]) for channel in ("tt", "te", "ee")}
        phiphi_delta = _max_rel(base["pp"], z4["pp"])
        lensed_delta = {channel: _max_rel(gr_lensed[channel], z4_lensed[channel]) for channel in ("tt", "te", "ee")}
        z4_te_zeros = _zeros(z4_lensed["te"], ell)
        te_zero_shift = max([abs(a - b) for a, b in zip(gr_te_zeros, z4_te_zeros)] or [0])
        tt_peak_shift = _peak(z4_lensed["tt"], ell, 30.0, 450.0) - _peak(gr_lensed["tt"], ell, 30.0, 450.0)
        ee_peak_shift = _peak(z4_lensed["ee"], ell, 30.0, 450.0) - _peak(gr_lensed["ee"], ell, 30.0, 450.0)
        finite = all(np.isfinite(z4[channel]).all() for channel in z4) and all(
            np.isfinite(z4_lensed[channel]).all() for channel in z4_lensed
        )
        positive_auto = bool(
            np.nanmin(z4["tt"][ell >= 2.0]) >= 0.0
            and np.nanmin(z4["ee"][ell >= 2.0]) >= 0.0
            and np.nanmin(z4["pp"][ell >= 2.0]) >= 0.0
            and np.nanmin(z4_lensed["tt"][ell >= 2.0]) >= 0.0
            and np.nanmin(z4_lensed["ee"][ell >= 2.0]) >= 0.0
        )
        continuity[str(lam)] = {
            "finite_all_spectra": finite,
            "no_negative_auto_spectra": positive_auto,
            "unlensed_primary_delta": primary_delta,
            "unlensed_primary_unchanged": max(primary_delta.values()) < 1.0e-14,
            "phiphi_delta": phiphi_delta,
            "lensed_delta": lensed_delta,
            "no_peak_jump": tt_peak_shift == 0 and ee_peak_shift == 0,
            "no_TE_zero_jump": te_zero_shift == 0,
            "ok": bool(finite and positive_auto and max(primary_delta.values()) < 1.0e-14 and tt_peak_shift == 0 and ee_peak_shift == 0 and te_zero_shift == 0),
        }
    return {
        "lambda_zero_max_rel_error": lambda_zero_errors,
        "lambda_zero_identity_passed": lambda_zero_identity,
        "small_lambda_scan": continuity,
        "small_lambda_continuity_passed": all(row["ok"] for row in continuity.values()),
    }


def build_payload() -> dict:
    baseline = baseline_payload()
    controlled = controlled_payload()
    weyl = weyl_payload()
    shape = shape_payload()
    spectra = _spectral_checks()
    shape_decomp = shape["shape_decomposition"]
    channel_policy = {
        "weyl_lensing_amplitude_delta_allowed": True,
        "weyl_lensing_shape_delta_enabled": True,
        "sw_isw_source_delta_enabled": False,
        "acoustic_phase_delta_enabled": False,
        "polarization_source_delta_enabled": False,
        "visibility_delta_enabled": False,
        "recombination_delta_enabled": False,
        "primordial_spectrum_delta_enabled": False,
        "hidden_sector_boltzmann_delta_enabled": False,
    }
    forbidden_channels_off = all(
        not channel_policy[key]
        for key in (
            "sw_isw_source_delta_enabled",
            "acoustic_phase_delta_enabled",
            "polarization_source_delta_enabled",
            "visibility_delta_enabled",
            "recombination_delta_enabled",
            "primordial_spectrum_delta_enabled",
            "hidden_sector_boltzmann_delta_enabled",
        )
    )
    shape_fraction = float(shape_decomp["shape_fraction"])
    shape_smooth = bool(
        0.05 < shape_fraction < 0.95
        and shape_decomp["shape_smoothness_score"] > 0.99
        and shape_decomp["shape_sign_changes"] <= 4
        and shape_decomp["shape_max_after_amplitude_subtraction"] < 0.02
    )
    eligibility = bool(
        baseline["safe_gr_baseline_available"]
        and controlled["controlled_z4_delta_gate_passed"]
        and not controlled["raw_native_los_used_for_planck"]
        and weyl["kernel"]["not_physical_shape_signature"]
        and shape["lensing_shape_delta_gate_passed"]
        and spectra["lambda_zero_identity_passed"]
        and spectra["small_lambda_continuity_passed"]
        and shape_smooth
        and forbidden_channels_off
    )
    return {
        "status": "janus-z4-nonzero-planck-eligibility-gate",
        "purpose": "authorize a first official nonzero-Z4 likelihood call; does not validate Planck fit",
        "backend": "camb_gr_plus_z4_delta",
        "z4_model_status": "effective_lensing_shape_trial",
        "full_native_z4_solver_used": False,
        "native_toy_los_used": False,
        "native_toy_los_planck_forbidden": True,
        "camb_gr_safe_baseline_roundtrip_passed": bool(baseline["safe_gr_baseline_available"]),
        "controlled_z4_delta_gate_passed": bool(controlled["controlled_z4_delta_gate_passed"]),
        "previous_weyl_delta_classification": weyl["kernel"]["current_delta_classification"],
        "lensing_shape_delta_gate_passed": bool(shape["lensing_shape_delta_gate_passed"]),
        "shape_fraction_min": 0.05,
        "shape_fraction_max": 0.95,
        "shape_smoothness_passed": shape_smooth,
        "shape_decomposition": shape_decomp,
        "channel_policy": channel_policy,
        "forbidden_channels_off": forbidden_channels_off,
        "phiphi_convention": "C_L_phiphi",
        "not_C_L_dd": True,
        "not_L4_C_L_phiphi": True,
        **spectra,
        "z4_planck_passed": False,
        "nonzero_z4_official_likelihood_allowed": eligibility,
        "first_allowed_planck_run_name": "official_planck_lensing_shape_delta_trial" if eligibility else None,
        "next_required_action": "run a small signed lambda_Z4 trial only through the allowed Weyl/lensing shape channel",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Nonzero Planck Eligibility Gate",
        "",
        f"Allowed: `{payload['nonzero_z4_official_likelihood_allowed']}`",
        f"Planck passed: `{payload['z4_planck_passed']}`",
        f"Backend: `{payload['backend']}`",
        f"Model status: `{payload['z4_model_status']}`",
        f"Native toy LOS used: `{payload['native_toy_los_used']}`",
        "",
        "## Criteria",
        f"- CAMB-GR safe baseline: `{payload['camb_gr_safe_baseline_roundtrip_passed']}`",
        f"- lambda=0 identity: `{payload['lambda_zero_identity_passed']}`",
        f"- small-lambda continuity: `{payload['small_lambda_continuity_passed']}`",
        f"- shape smoothness: `{payload['shape_smoothness_passed']}`",
        f"- forbidden channels off: `{payload['forbidden_channels_off']}`",
        "",
        "## First Allowed Use",
        f"`{payload['first_allowed_planck_run_name']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
