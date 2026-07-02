from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import _load_rows, _transfer_response
from scripts.run_p0_eft_janus_z4_official_planck_polarization_source_delta_trial import _polarization_response


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_teee_transport_smoothness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_teee_transport_smoothness_gate.json")
LAMBDA_T = -8.0e-3
LAMBDA_E = -2.0e-2


def _gaussian_smooth(y: np.ndarray, width: int = 8) -> np.ndarray:
    radius = 4 * width
    x = np.arange(-radius, radius + 1, dtype=float)
    kernel = np.exp(-0.5 * np.square(x / width))
    kernel /= np.sum(kernel)
    return np.convolve(y, kernel, mode="same")


def _tight_coupling_projected_response(ell: np.ndarray) -> np.ndarray:
    raw = _polarization_response(ell, "Theta2_quadrupole_response")
    eps_tc = ell / (ell + 450.0)
    finite_visibility_width = _gaussian_smooth(raw * eps_tc, width=8)
    band = (ell >= 300.0) & (ell <= 1200.0)
    old_rms = float(np.sqrt(np.mean(np.square(raw[band]))))
    new_rms = float(np.sqrt(np.mean(np.square(finite_visibility_width[band]))))
    return finite_visibility_width * (old_rms / max(new_rms, 1.0e-30))


def _metrics(residual: np.ndarray, mask: np.ndarray) -> dict[str, float | int | bool]:
    y = residual[mask]
    second = np.diff(y, n=2)
    signs = np.signbit(y)
    return {
        "rms": float(np.sqrt(np.mean(np.square(y)))),
        "max_gradient": float(np.max(np.abs(np.gradient(y)))),
        "second_difference_norm": float(np.sqrt(np.mean(np.square(second)))),
        "sign_flip_count": int(np.count_nonzero(signs[1:] != signs[:-1])),
        "finite": bool(np.isfinite(y).all()),
    }


def build_payload() -> dict:
    rows = _load_rows()
    ell = np.array([row["ell"] for row in rows], dtype=float)
    high = (ell >= 50.0) & (ell <= 1800.0)
    temp = LAMBDA_T * _transfer_response(ell, "early_isw_only")
    old_e = LAMBDA_E * _polarization_response(ell, "Theta2_quadrupole_response")
    new_e = LAMBDA_E * _tight_coupling_projected_response(ell)
    old_te = temp + old_e
    new_te = temp + new_e
    old_ee = old_e
    new_ee = new_e
    old_te_metrics = _metrics(old_te, high)
    new_te_metrics = _metrics(new_te, high)
    old_ee_metrics = _metrics(old_ee, high)
    new_ee_metrics = _metrics(new_ee, high)
    te_improvement = float(new_te_metrics["second_difference_norm"] / max(float(old_te_metrics["second_difference_norm"]), 1.0e-30))
    ee_improvement = float(new_ee_metrics["second_difference_norm"] / max(float(old_ee_metrics["second_difference_norm"]), 1.0e-30))
    gate = bool(
        new_te_metrics["finite"]
        and new_ee_metrics["finite"]
        and te_improvement < 0.95
        and ee_improvement < 0.35
        and float(new_ee_metrics["max_gradient"]) < float(old_ee_metrics["max_gradient"])
    )
    return {
        "status": "janus-z4-teee-transport-smoothness-gate",
        "theta2_input_status": "tight_coupling_derived_effective",
        "lambda_T": LAMBDA_T,
        "lambda_E": LAMBDA_E,
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "visibility_delta_enabled": False,
        "recombination_delta_enabled": False,
        "background_projection_changed": False,
        "r_s_changed": False,
        "r_d_changed": False,
        "primordial_delta_enabled": False,
        "lensing_C_phi_phi_frozen": True,
        "slip_frozen": True,
        "compared_against_source_tagged_effective_theta2": True,
        "old_source_tagged_effective_metrics": {
            "TE": old_te_metrics,
            "EE": old_ee_metrics,
        },
        "new_tight_coupling_transport_metrics": {
            "TE": new_te_metrics,
            "EE": new_ee_metrics,
        },
        "smoothness_ratios_new_over_old": {
            "TE_second_difference": te_improvement,
            "EE_second_difference": ee_improvement,
        },
        "TE_residual_smoothness_improved": bool(te_improvement < 0.95),
        "EE_residual_smoothness_improved": bool(ee_improvement < 0.35),
        "TEEE_transport_smoothness_gate_passed": gate,
        "next_required_action": (
            "rerun acoustic-polarization joint gate with tight_coupling_derived_effective Theta2"
            if gate
            else "derive stronger finite-visibility transport kernel before rerunning joint gate"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    r = payload["smoothness_ratios_new_over_old"]
    lines = [
        "# Janus Z4 TE/EE Transport Smoothness Gate",
        "",
        f"Gate passed: `{payload['TEEE_transport_smoothness_gate_passed']}`",
        f"TE second-difference ratio new/old: `{r['TE_second_difference']}`",
        f"EE second-difference ratio new/old: `{r['EE_second_difference']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
