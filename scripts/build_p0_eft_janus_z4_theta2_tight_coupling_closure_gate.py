from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_acoustic_driving_delta_gate import _acoustic_source
from scripts.build_p0_eft_janus_z4_weyl_late_isw_consistency_gate import _grid


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_theta2_tight_coupling_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_theta2_tight_coupling_closure_gate.json")


def _theta2_tight_coupling_source(k: np.ndarray, tau: np.ndarray) -> dict[str, np.ndarray]:
    acoustic = _acoustic_source(k, tau)
    kappadot = 55.0 + 850.0 * np.exp(-0.5 * ((tau - 0.52) / 0.075) ** 2)
    epsilon_tc = k[:, np.newaxis] / kappadot[np.newaxis, :]
    metric_drive = acoustic["delta_phi"] + acoustic["delta_psi"]
    velocity_proxy = np.gradient(metric_drive, tau, axis=1, edge_order=2)
    isw_proxy = np.gradient(velocity_proxy, tau, axis=1, edge_order=2)
    visibility_window = acoustic["acoustic_window"][np.newaxis, :] * acoustic["e_minus_kappa"][np.newaxis, :]
    theta2 = epsilon_tc * visibility_window * (velocity_proxy + 0.25 * isw_proxy)
    return {
        "theta2": theta2,
        "epsilon_tc": epsilon_tc,
        "visibility_window": visibility_window,
        "metric_drive": metric_drive,
        "velocity_proxy": velocity_proxy,
        "kappadot": kappadot,
    }


def _roughness(arr: np.ndarray, axis: int) -> float:
    return float(np.sqrt(np.mean(np.square(np.diff(arr, n=2, axis=axis)))))


def build_payload() -> dict:
    k, tau = _grid()
    data = _theta2_tight_coupling_source(k, tau)
    theta2 = data["theta2"]
    eps = data["epsilon_tc"]
    visibility = data["visibility_window"]
    strong_tc = eps < np.quantile(eps, 0.12)
    peak = visibility > 0.65 * float(np.max(visibility))
    vanish_ratio = float(np.max(np.abs(theta2[strong_tc])) / max(np.max(np.abs(theta2)), 1.0e-30))
    regular_peak = bool(np.isfinite(theta2[:, peak[0]]).all())
    smooth_k = _roughness(theta2, axis=0)
    smooth_tau = _roughness(theta2, axis=1)
    gate = bool(
        np.isfinite(theta2).all()
        and vanish_ratio < 0.08
        and regular_peak
        and smooth_k < 1.0e-3
        and smooth_tau < 2.0e-3
    )
    return {
        "status": "janus-z4-theta2-tight-coupling-closure-gate",
        "theta2_previous_status": "source_tagged_effective",
        "theta2_new_status": "tight_coupling_derived_effective" if gate else "tight_coupling_candidate_failed",
        "boltzmann_hierarchy_closed": False,
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
        "metric_split_respected": True,
        "theta2_depends_on_k_over_kappadot": True,
        "theta2_depends_on_velocity_or_dipole": True,
        "theta2_depends_on_metric_driving": True,
        "theta2_arbitrary_ell_function": False,
        "theta2_response_vanishes_as_k_over_kappadot_to_zero": bool(vanish_ratio < 0.08),
        "theta2_response_regular_when_visibility_peaks": regular_peak,
        "theta2_response_smooth_in_k": bool(smooth_k < 1.0e-3),
        "theta2_response_smooth_in_tau": bool(smooth_tau < 2.0e-3),
        "diagnostics": {
            "vanish_ratio_strong_tight_coupling": vanish_ratio,
            "second_difference_norm_k": smooth_k,
            "second_difference_norm_tau": smooth_tau,
            "max_abs_theta2": float(np.max(np.abs(theta2))),
            "max_epsilon_tc": float(np.max(eps)),
        },
        "theta2_tight_coupling_closure_gate_passed": gate,
        "next_required_action": (
            "run TEEETransportSmoothnessGate with tight_coupling_derived_effective Theta2"
            if gate
            else "fix tight-coupling source regularity before any TE/EE transport gate"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    d = payload["diagnostics"]
    lines = [
        "# Janus Z4 Theta2 Tight-Coupling Closure Gate",
        "",
        f"Gate passed: `{payload['theta2_tight_coupling_closure_gate_passed']}`",
        f"New status: `{payload['theta2_new_status']}`",
        f"Vanish ratio strong tight-coupling: `{d['vanish_ratio_strong_tight_coupling']}`",
        f"Second-difference norm k: `{d['second_difference_norm_k']}`",
        f"Second-difference norm tau: `{d['second_difference_norm_tau']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
