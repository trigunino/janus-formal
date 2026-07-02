from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import (
    CHANNELS,
    OLD_NO_SLIP_PARALLEL_FRACTION,
    _projection_stats,
    _tangent_matrix,
    _unit,
)
from scripts.build_p0_eft_janus_z4_derived_slip_source_level_regeneration_gate import _slip_sources
from scripts.build_p0_eft_janus_z4_derived_slip_surface_sw_consistency_gate import build_payload as sw_blocker_payload
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import FROZEN_LAMBDA_T
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows
from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_photon_monopole_sw_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_photon_monopole_sw_closure_gate.json")
SURFACE_INTERESTING_THRESHOLD = 0.70
PHOTON_BARYON_K = 0.7


def _gradient(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    return np.gradient(y, x, edge_order=1)


def _visibility_window(tau: np.ndarray) -> np.ndarray:
    center = 0.5 * (float(tau[0]) + float(tau[-1]))
    width = max(float(tau[-1] - tau[0]) / 6.0, 1.0e-12)
    window = np.exp(-np.square((tau - center) / width))
    return window / max(float(np.max(window)), 1.0e-12)


def _interpolate_to_ells(values: np.ndarray, ells: np.ndarray) -> np.ndarray:
    x = np.linspace(float(ells[0]), float(ells[-1]), len(values))
    return np.interp(ells, x, values)


def _surface_sources() -> dict[str, np.ndarray]:
    payload = _slip_sources(CosmologyPoint())["source_payload"]
    tau = np.asarray(payload["time_grid"], dtype=float)
    delta_psi = np.asarray(payload["deltaPsi_Z4"], dtype=float)
    delta_phi_dot = np.asarray(payload["deltaPhiDot_Z4"], dtype=float)
    visibility = _visibility_window(tau)

    delta_theta0 = -0.5 * delta_psi - 0.25 * np.cumsum(delta_phi_dot) * (tau[1] - tau[0])
    delta_v_b = -_gradient(tau, delta_theta0 + delta_psi) / PHOTON_BARYON_K
    doppler_source = _gradient(tau, visibility * delta_v_b) / PHOTON_BARYON_K

    potential_only = visibility * delta_psi
    monopole_plus_potential = visibility * (delta_theta0 + delta_psi)
    full_surface = monopole_plus_potential + doppler_source
    return {
        "potential_only": potential_only,
        "monopole_plus_potential": monopole_plus_potential,
        "full_surface": full_surface,
        "deltaTheta0_Z4": delta_theta0,
        "deltaVb_Z4": delta_v_b,
        "Doppler_Z4": doppler_source,
    }


def _delta_from_surface(reference: list[dict[str, float]], values: np.ndarray) -> dict[str, np.ndarray]:
    arrays = _rows_to_arrays(reference)
    shape = _unit(_interpolate_to_ells(values, arrays["ell"]))
    zero = np.zeros_like(shape)
    return {
        "cl_tt": FROZEN_LAMBDA_T * arrays["cl_tt"] * shape,
        "cl_te": 0.5 * FROZEN_LAMBDA_T * arrays["cl_te"] * shape,
        "cl_ee": zero,
    }


def build_payload() -> dict:
    blocker = sw_blocker_payload()
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    sources = _surface_sources()

    projections = {}
    for name in ("potential_only", "monopole_plus_potential", "full_surface"):
        vector = _flatten(_delta_from_surface(reference, sources[name]), scales)
        projections[name] = _projection_stats(vector, matrix, tangent_norms)

    full_parallel = projections["full_surface"]["parallel_fraction"]
    closure_passed = bool(
        blocker["surface_term_parallel_fraction_recorded"]
        and blocker["full_derived_slip_archived"]
        and full_parallel < OLD_NO_SLIP_PARALLEL_FRACTION
    )
    return {
        "status": "janus-z4-derived-slip-photon-monopole-sw-closure-gate",
        "deltaPsi_Z4_from_derived_slip": True,
        "deltaPhi_Z4_from_derived_slip": True,
        "photon_monopole_response_declared": True,
        "deltaTheta0_Z4_free": False,
        "deltaTheta0_response_equation": "deltaTheta0_Z4 = -0.5*deltaPsi_Z4 - 0.25*integral(deltaPhiDot_Z4 d_tau)",
        "doppler_response_declared": True,
        "Doppler_Z4_free": False,
        "doppler_policy": "derived_from_photon_baryon_velocity_response",
        "doppler_response_equation": "Doppler_Z4 = d_tau(g*v_b_Z4)/k, v_b_Z4 = -d_tau(deltaTheta0_Z4 + deltaPsi_Z4)/k",
        "surface_SW_source": "g*(deltaTheta0_Z4 + deltaPsi_Z4)",
        "full_surface_source": "g*(deltaTheta0_Z4 + deltaPsi_Z4) + Doppler_Z4",
        "gauge_convention_declared": True,
        "gauge_convention": "Newtonian gauge, fixed visibility and recombination",
        "visibility_frozen": True,
        "recombination_frozen": True,
        "tight_coupling_policy_declared": True,
        "potential_only_parallel_fraction": projections["potential_only"]["parallel_fraction"],
        "monopole_plus_potential_parallel_fraction": projections["monopole_plus_potential"]["parallel_fraction"],
        "full_surface_parallel_fraction": full_parallel,
        "potential_only_perpendicular_fraction": projections["potential_only"]["perpendicular_fraction"],
        "monopole_plus_potential_perpendicular_fraction": projections["monopole_plus_potential"]["perpendicular_fraction"],
        "full_surface_perpendicular_fraction": projections["full_surface"]["perpendicular_fraction"],
        "dominant_tangent_direction_full_surface": projections["full_surface"]["dominant_tangent_direction"],
        "subchannel_projection": projections,
        "surface_SW_physical_closure": closure_passed,
        "full_surface_less_tangent_than_no_slip": full_parallel < OLD_NO_SLIP_PARALLEL_FRACTION,
        "full_surface_interesting": full_parallel < SURFACE_INTERESTING_THRESHOLD,
        "Planck_trial_allowed": False,
        "diagnostic_surface_only_trial_allowed": False,
        "no_lambda_retuning": True,
        "no_free_slip_parameter": True,
        "no_free_eta_ratio": True,
        "no_direct_Cl_patch": True,
        "raw_toy_LOS_forbidden": True,
        "next_required_gate": "P0EFTJanusZ4DerivedSlipSurfaceCarrierTangentProjectionGate"
        if closure_passed
        else "archive_surface_SW_if_full_surface_is_carrier_tangent",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Derived Slip Photon Monopole SW Closure Gate",
        "",
        f"Surface SW physical closure: `{payload['surface_SW_physical_closure']}`",
        f"Potential-only parallel: `{payload['potential_only_parallel_fraction']}`",
        f"Monopole+potential parallel: `{payload['monopole_plus_potential_parallel_fraction']}`",
        f"Full-surface parallel: `{payload['full_surface_parallel_fraction']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
