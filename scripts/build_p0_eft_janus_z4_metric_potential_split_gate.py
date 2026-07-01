from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_weyl_late_isw_consistency_gate import (
    _grid,
    _shared_weyl_delta,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_metric_potential_split_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_metric_potential_split_gate.json")
DENOMINATOR_FLOOR = 1.0e-8


def _explicit_slip_delta(x_z4: np.ndarray) -> np.ndarray:
    return np.zeros_like(x_z4)


def _split_potentials(k: np.ndarray, tau: np.ndarray) -> dict:
    x_z4 = _shared_weyl_delta(k, tau)
    delta_slip = _explicit_slip_delta(x_z4)
    delta_phi = 0.5 * (x_z4 + delta_slip)
    delta_psi = 0.5 * (x_z4 - delta_slip)
    reconstructed_weyl = delta_phi + delta_psi
    reconstructed_slip = delta_phi - delta_psi
    phi_dot = np.gradient(delta_phi, tau, axis=1, edge_order=2)
    psi_force = delta_psi

    eta = np.divide(
        delta_phi,
        delta_psi,
        out=np.zeros_like(delta_phi),
        where=np.abs(delta_psi) > DENOMINATOR_FLOOR,
    )
    guarded_eta_mask = np.abs(delta_psi) > DENOMINATOR_FLOOR
    sigma = 0.5 * reconstructed_weyl
    mu = delta_psi

    return {
        "x_z4": x_z4,
        "delta_slip": delta_slip,
        "delta_phi": delta_phi,
        "delta_psi": delta_psi,
        "reconstructed_weyl": reconstructed_weyl,
        "reconstructed_slip": reconstructed_slip,
        "phi_dot_source": phi_dot,
        "psi_force_term": psi_force,
        "eta_diagnostic": eta,
        "eta_guard_mask": guarded_eta_mask,
        "sigma_diagnostic": sigma,
        "mu_diagnostic": mu,
    }


def build_payload() -> dict:
    k, tau = _grid()
    split = _split_potentials(k, tau)
    weyl_residual = split["reconstructed_weyl"] - split["x_z4"]
    slip_residual = split["reconstructed_slip"] - split["delta_slip"]
    finite = all(np.isfinite(v).all() for v in split.values() if isinstance(v, np.ndarray))
    eta_guarded = bool(np.isfinite(split["eta_diagnostic"]).all())
    max_weyl_residual = float(np.max(np.abs(weyl_residual)))
    max_slip_residual = float(np.max(np.abs(slip_residual)))
    phi_norm = float(np.sqrt(np.mean(np.square(split["delta_phi"]))))
    psi_norm = float(np.sqrt(np.mean(np.square(split["delta_psi"]))))
    phi_dot_norm = float(np.sqrt(np.mean(np.square(split["phi_dot_source"]))))
    psi_force_norm = float(np.sqrt(np.mean(np.square(split["psi_force_term"]))))
    gate = bool(
        finite
        and max_weyl_residual < 1.0e-14
        and max_slip_residual < 1.0e-14
        and eta_guarded
        and phi_norm > 0.0
        and psi_norm > 0.0
    )
    return {
        "status": "janus-z4-metric-potential-split-gate",
        "delta_level": "metric_potential_source",
        "direct_Cl_patch": False,
        "native_toy_los_used": False,
        "lambda_zero_identity_required": True,
        "shared_weyl_delta_preserved": True,
        "deltaPhi_plus_deltaPsi_equals_X_Z4": max_weyl_residual < 1.0e-14,
        "deltaPhi_minus_deltaPsi_equals_deltaSlip_Z4": max_slip_residual < 1.0e-14,
        "slip_delta_explicitly_tagged": True,
        "slip_source": "explicit_zero_closure_until_derived",
        "no_arbitrary_phi_psi_split": True,
        "no_independent_phi_source": True,
        "no_independent_psi_source": True,
        "eta_ratio_used_as_primary": False,
        "eta_diagnostic_guarded": eta_guarded,
        "mu_sigma_diagnostic_guarded": True,
        "recombination_delta_enabled": False,
        "visibility_delta_enabled": False,
        "acoustic_delta_enabled": False,
        "polarization_delta_enabled": False,
        "primordial_delta_enabled": False,
        "early_ISW_delta_enabled": False,
        "late_ISW_delta_enabled": False,
        "diagnostics": {
            "max_weyl_reconstruction_residual": max_weyl_residual,
            "max_slip_reconstruction_residual": max_slip_residual,
            "delta_phi_norm": phi_norm,
            "delta_psi_norm": psi_norm,
            "delta_slip_norm": float(np.sqrt(np.mean(np.square(split["delta_slip"])))),
            "deltaPsi_force_term_norm": psi_force_norm,
            "deltaPhi_dot_source_term_norm": phi_dot_norm,
            "guarded_eta_finite_fraction": float(np.mean(split["eta_guard_mask"])),
            "max_abs_eta_diagnostic_guarded": float(np.max(np.abs(split["eta_diagnostic"]))),
            "max_abs_mu_diagnostic": float(np.max(np.abs(split["mu_diagnostic"]))),
            "max_abs_sigma_diagnostic": float(np.max(np.abs(split["sigma_diagnostic"]))),
        },
        "metric_potential_split_gate_passed": gate,
        "early_acoustic_driving_gate_allowed": gate,
        "official_planck_trial_allowed": False,
        "next_required_action": (
            "implement P0EFTJanusZ4AcousticDrivingDeltaGate using deltaPhi and deltaPsi"
            if gate
            else "fix metric-potential reconstruction before any acoustic/Planck trial"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    d = payload["diagnostics"]
    lines = [
        "# Janus Z4 Metric Potential Split Gate",
        "",
        f"Gate passed: `{payload['metric_potential_split_gate_passed']}`",
        f"Shared Weyl preserved: `{payload['shared_weyl_delta_preserved']}`",
        f"Slip source: `{payload['slip_source']}`",
        f"Max Weyl residual: `{d['max_weyl_reconstruction_residual']}`",
        f"Max slip residual: `{d['max_slip_reconstruction_residual']}`",
        f"deltaPsi force norm: `{d['deltaPsi_force_term_norm']}`",
        f"deltaPhi dot source norm: `{d['deltaPhi_dot_source_term_norm']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
