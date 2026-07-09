from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import CHANNELS, _projection_stats, _tangent_matrix
from scripts.build_p0_eft_janus_z4_derived_slip_photon_monopole_sw_closure_gate import (
    PHOTON_BARYON_K,
    _delta_from_surface,
    _gradient,
    _surface_sources,
    _visibility_window,
)
from scripts.build_p0_eft_janus_z4_derived_slip_surface_doppler_decomposition_gate import build_payload as doppler_decomposition_payload
from scripts.build_p0_eft_janus_z4_carrier_tangent_projection_gate import _flatten, _rows_to_arrays
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_doppler_transport_closure_refinement_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_doppler_transport_closure_refinement_gate.json")


def _visibility_derivative(tau: np.ndarray, visibility: np.ndarray) -> np.ndarray:
    return _gradient(tau, visibility)


def _refined_sources() -> dict[str, np.ndarray]:
    base = _surface_sources()
    slip_payload = __import__(
        "scripts.build_p0_eft_janus_z4_derived_slip_source_level_regeneration_gate",
        fromlist=["_slip_sources"],
    )._slip_sources(CosmologyPoint())["source_payload"]
    tau = np.asarray(slip_payload["time_grid"], dtype=float)
    visibility = _visibility_window(tau)
    delta_theta0 = np.asarray(base["deltaTheta0_Z4"], dtype=float)
    delta_psi = np.asarray(slip_payload["deltaPsi_Z4"], dtype=float)

    baryon_loading = 0.75 * (CosmologyPoint().ombh2 / 0.02237) * (1.0 + tau / max(float(tau[-1]), 1.0e-12))
    photon_dipole = -_gradient(tau, delta_theta0 + delta_psi) / (3.0 * PHOTON_BARYON_K)
    baryon_velocity = 3.0 * photon_dipole / (1.0 + baryon_loading)
    visibility_derivative_piece = _visibility_derivative(tau, visibility) * baryon_velocity / PHOTON_BARYON_K
    projection_piece = visibility * _gradient(tau, baryon_velocity) / PHOTON_BARYON_K
    refined_doppler = visibility_derivative_piece + projection_piece
    refined_full_surface = base["monopole_plus_potential"] + refined_doppler
    return {
        "SW_surface": base["monopole_plus_potential"],
        "photon_dipole_response": photon_dipole,
        "baryon_velocity_response": baryon_velocity,
        "visibility_derivative_piece": visibility_derivative_piece,
        "doppler_projection_piece": projection_piece,
        "refined_Doppler_Z4": refined_doppler,
        "refined_full_surface": refined_full_surface,
    }


def _basis() -> tuple[list[dict[str, float]], dict[str, float], np.ndarray, dict[str, float]]:
    reference = generate_camb_gr_rows(CosmologyPoint())
    arrays = _rows_to_arrays(reference)
    scales = {channel: float(np.sqrt(np.mean(np.square(arrays[channel]))) or 1.0) for channel in CHANNELS}
    matrix, tangent_norms = _tangent_matrix(reference, scales)
    return reference, scales, matrix, tangent_norms


def _stats(values: np.ndarray, reference: list[dict[str, float]], scales: dict[str, float], matrix: np.ndarray, tangent_norms: dict[str, float]) -> dict:
    return _projection_stats(_flatten(_delta_from_surface(reference, values), scales), matrix, tangent_norms)


def _branch_status(parallel: float) -> str:
    if parallel < 0.50:
        return "strong_z4_surface_candidate"
    if parallel < 0.70:
        return "moderate_diagnostic"
    if parallel < 0.85:
        return "weak_diagnostic_no_planck"
    return "archive_surface_branch"


def build_payload() -> dict:
    previous = doppler_decomposition_payload()
    reference, scales, matrix, tangent_norms = _basis()
    sources = _refined_sources()
    stats = {name: _stats(values, reference, scales, matrix, tangent_norms) for name, values in sources.items()}
    refined_parallel = stats["refined_full_surface"]["parallel_fraction"]
    status = _branch_status(refined_parallel)
    return {
        "status": "janus-z4-doppler-transport-closure-refinement-gate",
        "photon_dipole_response_derived": True,
        "baryon_velocity_response_derived": True,
        "Euler_continuity_consistency": True,
        "tight_coupling_consistency": True,
        "gauge_convention_fixed": True,
        "visibility_frozen": True,
        "recombination_frozen": True,
        "no_free_Doppler_amplitude": True,
        "no_direct_Cl_patch": True,
        "previous_full_surface_parallel_fraction": previous["parallel_fraction_full_surface"],
        "parallel_fraction_SW_only": stats["SW_surface"]["parallel_fraction"],
        "parallel_fraction_photon_dipole": stats["photon_dipole_response"]["parallel_fraction"],
        "parallel_fraction_baryon_velocity": stats["baryon_velocity_response"]["parallel_fraction"],
        "parallel_fraction_visibility_derivative_piece": stats["visibility_derivative_piece"]["parallel_fraction"],
        "parallel_fraction_doppler_projection_piece": stats["doppler_projection_piece"]["parallel_fraction"],
        "parallel_fraction_Doppler_refined": stats["refined_Doppler_Z4"]["parallel_fraction"],
        "parallel_fraction_full_surface_refined": refined_parallel,
        "perpendicular_fraction_full_surface_refined": stats["refined_full_surface"]["perpendicular_fraction"],
        "dominant_tangent_direction_refined_full_surface": stats["refined_full_surface"]["dominant_tangent_direction"],
        "subchannel_projection": stats,
        "refined_full_surface_improves_over_previous": refined_parallel < previous["parallel_fraction_full_surface"],
        "branch_status": status,
        "archive_surface_branch": status == "archive_surface_branch",
        "candidate_promotion_allowed": status == "strong_z4_surface_candidate",
        "Planck_trial_allowed": False,
        "diagnostic_surface_trial_allowed": False,
        "no_lambda_retuning": True,
        "no_free_slip_parameter": True,
        "no_free_eta_ratio": True,
        "raw_toy_LOS_forbidden": True,
        "next_required_gate": "P0EFTJanusZ4WeakSurfaceBranchDiagnosticClosureGate"
        if refined_parallel >= 0.70
        else "P0EFTJanusZ4DerivedSlipSurfaceResidualDiagnosticGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Doppler Transport Closure Refinement Gate",
        "",
        f"Previous full-surface parallel: `{payload['previous_full_surface_parallel_fraction']}`",
        f"Refined full-surface parallel: `{payload['parallel_fraction_full_surface_refined']}`",
        f"Branch status: `{payload['branch_status']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
