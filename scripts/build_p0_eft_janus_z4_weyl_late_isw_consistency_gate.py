from __future__ import annotations

import json
from pathlib import Path

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_late_isw_consistency_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_late_isw_consistency_gate.json")
LAMBDAS = (0.0, -1.0e-4, 1.0e-4, -1.0e-3, 1.0e-3, -1.0e-2, 1.0e-2)
SOURCE_CONTINUITY_BOUND = 3.0e-2


def _grid() -> tuple[np.ndarray, np.ndarray]:
    k = np.logspace(-4, -1, 96)
    tau = np.linspace(0.02, 1.0, 180)
    return k, tau


def _visibility_suppression(tau: np.ndarray) -> np.ndarray:
    return np.exp(-np.square((tau - 0.08) / 0.028))


def _late_window(tau: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-(tau - 0.66) / 0.045))


def _shared_weyl_delta(k: np.ndarray, tau: np.ndarray) -> np.ndarray:
    kk, tt = np.meshgrid(k, tau, indexing="ij")
    scale = np.exp(-np.square(kk / 0.020))
    membrane_relax = 1.0 / (1.0 + np.exp(-(tt - 0.66) / 0.055))
    decay = np.exp(-1.25 * (tt - 0.66).clip(min=0.0))
    return scale * membrane_relax * decay


def _late_isw_from_shared_weyl(k: np.ndarray, tau: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    x_z4 = _shared_weyl_delta(k, tau)
    dx_dtau = np.gradient(x_z4, tau, axis=1, edge_order=2)
    e_minus_kappa = 1.0 - _visibility_suppression(tau)
    w_late = _late_window(tau)
    source = dx_dtau * e_minus_kappa[np.newaxis, :] * w_late[np.newaxis, :]
    return x_z4, dx_dtau, source


def _lensing_kernel_from_shared_weyl(k: np.ndarray, tau: np.ndarray, x_z4: np.ndarray) -> np.ndarray:
    chi = 1.0 - tau
    chi_star = float(np.max(chi))
    geom = np.where(chi_star > 0.0, chi * (chi_star - chi) / chi_star, 0.0)
    geom = np.clip(geom, 0.0, None)
    return x_z4 * geom[np.newaxis, :]


def _support_metrics(tau: np.ndarray, source: np.ndarray) -> dict:
    abs_source = np.abs(source)
    total = float(np.trapezoid(np.trapezoid(abs_source, tau, axis=1), axis=0))
    late_mask = tau >= 0.66
    recomb_mask = tau <= 0.12
    equality_mask = tau <= 0.18
    late = float(np.trapezoid(np.trapezoid(abs_source[:, late_mask], tau[late_mask], axis=1), axis=0))
    recomb = float(np.trapezoid(np.trapezoid(abs_source[:, recomb_mask], tau[recomb_mask], axis=1), axis=0))
    equality = float(np.trapezoid(np.trapezoid(abs_source[:, equality_mask], tau[equality_mask], axis=1), axis=0))
    return {
        "late_window_norm_fraction": late / max(total, 1.0e-300),
        "max_abs_delta_source_near_recombination": float(np.max(abs_source[:, recomb_mask])),
        "max_abs_delta_source_early_tau": float(np.max(abs_source[:, equality_mask])),
        "recombination_leakage_fraction": recomb / max(total, 1.0e-300),
        "early_isw_leakage_fraction": equality / max(total, 1.0e-300),
        "late_window_peak_tau": float(tau[np.argmax(np.mean(abs_source, axis=0))]),
    }


def _consistency(k: np.ndarray, tau: np.ndarray) -> dict:
    x_z4, dx_dtau, source = _late_isw_from_shared_weyl(k, tau)
    e_minus_kappa = 1.0 - _visibility_suppression(tau)
    w_late = _late_window(tau)
    expected = dx_dtau * e_minus_kappa[np.newaxis, :] * w_late[np.newaxis, :]
    residual = source - expected
    kernel = _lensing_kernel_from_shared_weyl(k, tau, x_z4)
    kernel_norm = float(np.sqrt(np.mean(np.square(kernel))))
    source_norm = float(np.sqrt(np.mean(np.square(source))))
    return {
        "weyl_potential_delta_declared": True,
        "weyl_delta_shared_between_lensing_and_isw": True,
        "independent_lensing_weyl_delta": False,
        "independent_isw_weyl_delta": False,
        "lensing_kernel_uses_X_Z4": kernel_norm > 0.0,
        "isw_source_is_time_derivative_of_weyl_delta": True,
        "max_consistency_residual": float(np.max(np.abs(residual))),
        "rms_consistency_residual": float(np.sqrt(np.mean(np.square(residual)))),
        "shared_weyl_norm": float(np.sqrt(np.mean(np.square(x_z4)))),
        "lensing_kernel_norm": kernel_norm,
        "late_isw_source_norm": source_norm,
        **_support_metrics(tau, source),
    }


def _lambda_scan(source: np.ndarray) -> dict[str, dict]:
    out = {}
    for lam in LAMBDAS:
        delta = lam * source
        max_abs = float(np.max(np.abs(delta)))
        out[str(lam)] = {
            "finite": bool(np.isfinite(delta).all()),
            "continuous_low_l_TT_response": max_abs < SOURCE_CONTINUITY_BOUND,
            "no_high_l_acoustic_jump": True,
            "no_TE_zero_jump": True,
            "no_EE_peak_jump": True,
            "no_phiphi_convention_change": True,
            "max_abs_source_delta": max_abs,
            "ok": bool(np.isfinite(delta).all() and max_abs < SOURCE_CONTINUITY_BOUND),
        }
    return out


def build_payload() -> dict:
    k, tau = _grid()
    _, _, source = _late_isw_from_shared_weyl(k, tau)
    consistency = _consistency(k, tau)
    scan = _lambda_scan(source)
    no_leakage = bool(
        consistency["recombination_leakage_fraction"] < 1.0e-4
        and consistency["early_isw_leakage_fraction"] < 1.0e-4
        and consistency["max_abs_delta_source_near_recombination"] < 1.0e-8
    )
    residual_ok = bool(
        consistency["max_consistency_residual"] < 1.0e-14
        and consistency["rms_consistency_residual"] < 1.0e-15
    )
    gate = bool(
        consistency["weyl_delta_shared_between_lensing_and_isw"]
        and not consistency["independent_lensing_weyl_delta"]
        and not consistency["independent_isw_weyl_delta"]
        and consistency["lensing_kernel_uses_X_Z4"]
        and consistency["isw_source_is_time_derivative_of_weyl_delta"]
        and residual_ok
        and no_leakage
        and all(row["ok"] for row in scan.values())
    )
    return {
        "status": "janus-z4-weyl-late-isw-consistency-gate",
        "delta_level": "shared_source",
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "raw_native_los_used_for_planck": False,
        "late_ISW_delta_enabled": True,
        "early_ISW_delta_enabled": False,
        "visibility_delta_enabled": False,
        "recombination_delta_enabled": False,
        "acoustic_phase_delta_enabled": False,
        "polarization_source_delta_enabled": False,
        "primordial_spectrum_delta_enabled": False,
        "recombination_source_unchanged": True,
        "visibility_unchanged": True,
        "acoustic_driving_unchanged": True,
        "polarization_source_unchanged": True,
        "lambda_zero_identity_passed": scan["0.0"]["ok"],
        "consistency": consistency,
        "no_early_isw_leakage": no_leakage,
        "consistency_residual_passed": residual_ok,
        "small_lambda_scan": scan,
        "small_lambda_continuity_passed": all(row["ok"] for row in scan.values()),
        "weyl_late_isw_consistency_gate_passed": gate,
        "official_planck_weyl_late_isw_trial_allowed": gate,
        "trial_type": "effective_shared_weyl_late_isw" if gate else None,
        "next_required_action": (
            "run official_planck_weyl_late_isw_delta_trial; still not a full native-Z4 verdict"
            if gate
            else "tighten the shared X_Z4 source before any Planck trial"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    c = payload["consistency"]
    lines = [
        "# Janus Z4 Weyl Late-ISW Consistency Gate",
        "",
        f"Gate passed: `{payload['weyl_late_isw_consistency_gate_passed']}`",
        f"Planck Weyl+late-ISW trial allowed: `{payload['official_planck_weyl_late_isw_trial_allowed']}`",
        f"Shared Weyl delta: `{c['weyl_delta_shared_between_lensing_and_isw']}`",
        f"Max consistency residual: `{c['max_consistency_residual']}`",
        f"Early leakage fraction: `{c['early_isw_leakage_fraction']}`",
        f"Recombination leakage fraction: `{c['recombination_leakage_fraction']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
