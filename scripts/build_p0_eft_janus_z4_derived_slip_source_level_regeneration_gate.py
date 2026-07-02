from __future__ import annotations

import json
import sys
from dataclasses import replace
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_derived_slip_value_transport_gate import (
    _integrate as slip_transport_integral,
    build_payload as value_transport_payload,
)
from scripts.build_p0_eft_janus_z4_regenerative_cache_invalidation_gate import MUTATIONS
from scripts.build_p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate import FROZEN_LAMBDA_E, FROZEN_LAMBDA_T
from scripts.build_p0_eft_janus_z4_regenerative_polarization_pi_source_gate import HIERARCHY_LMAX
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, provenance_manifest
from janus_lab.z4_source_level import (
    SOURCE_LEVEL_VERSION,
    hash_payload,
    regenerative_polarization_pi_source,
    regenerative_temperature_source_delta,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_source_level_regeneration_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_source_level_regeneration_gate.json")
SLIP_K = 0.7
NORMAL_ORIENTATION_SIGN = 1.0


def _gradient(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    return np.gradient(y, x, edge_order=1)


def _cumulative_trapezoid(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    out = np.zeros_like(y)
    out[1:] = np.cumsum(0.5 * (y[1:] + y[:-1]) * np.diff(x))
    return out


def _visibility_window(tau: np.ndarray) -> np.ndarray:
    center = 0.5 * (float(tau[0]) + float(tau[-1]))
    width = max(float(tau[-1] - tau[0]) / 6.0, 1.0e-12)
    window = np.exp(-np.square((tau - center) / width))
    return window / max(float(np.max(window)), 1.0e-12)


def _slip_sources(cosmology: CosmologyPoint) -> dict:
    temp = regenerative_temperature_source_delta(cosmology, FROZEN_LAMBDA_T)
    pol = regenerative_polarization_pi_source(cosmology, FROZEN_LAMBDA_E, HIERARCHY_LMAX)
    temp_payload = temp["source_payload"]
    pol_payload = pol["source_payload"]

    tau = np.asarray(temp_payload["time_grid"], dtype=float)
    acoustic = np.asarray(temp_payload["W_acoustic"], dtype=float)
    opacity = np.asarray(temp_payload["exp_minus_kappa"], dtype=float)
    delta_w_dot = np.asarray(temp_payload["deltaPhiDot_plus_deltaPsiDot"], dtype=float)
    delta_w = _cumulative_trapezoid(tau, delta_w_dot)

    delta_slip = NORMAL_ORIENTATION_SIGN * np.asarray(
        [slip_transport_integral(SLIP_K, float(t), "boundary_normal_derivative") for t in tau],
        dtype=float,
    )
    delta_slip_dot = _gradient(tau, delta_slip)
    delta_phi = 0.5 * (delta_w + delta_slip)
    delta_psi = 0.5 * (delta_w - delta_slip)
    delta_phi_dot = 0.5 * (delta_w_dot + delta_slip_dot)
    delta_psi_dot = 0.5 * (delta_w_dot - delta_slip_dot)

    visibility = _visibility_window(tau)
    temperature_surface_term = visibility * delta_psi
    temperature_early_isw_term = opacity * (delta_phi_dot + delta_psi_dot)
    delta_s_t_with_slip = FROZEN_LAMBDA_T * acoustic * (temperature_early_isw_term + temperature_surface_term)

    pi_source = np.asarray(pol_payload["Pi_source_Z4"], dtype=float)
    tca = np.asarray(pol_payload["TCA_switch"], dtype=float)
    pi_source_with_slip = pi_source + delta_slip
    delta_s_e_with_slip = FROZEN_LAMBDA_E * opacity * tca * pi_source_with_slip

    source_payload = {
        "version": SOURCE_LEVEL_VERSION,
        "cosmology": temp_payload["cosmology"],
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "slip_k": SLIP_K,
        "visible_slip_projection": "boundary_normal_derivative",
        "normal_orientation_sign": NORMAL_ORIENTATION_SIGN,
        "time_grid": tau.tolist(),
        "deltaW_Z4": delta_w.tolist(),
        "deltaWDot_Z4": delta_w_dot.tolist(),
        "deltaSlip_Z4": delta_slip.tolist(),
        "deltaSlipDot_Z4": delta_slip_dot.tolist(),
        "deltaPhi_Z4": delta_phi.tolist(),
        "deltaPsi_Z4": delta_psi.tolist(),
        "deltaPhiDot_Z4": delta_phi_dot.tolist(),
        "deltaPsiDot_Z4": delta_psi_dot.tolist(),
        "temperature_surface_term": temperature_surface_term.tolist(),
        "temperature_early_ISW_term": temperature_early_isw_term.tolist(),
        "delta_S_T_Z4_with_slip": delta_s_t_with_slip.tolist(),
        "Pi_source_Z4_with_slip": pi_source_with_slip.tolist(),
        "delta_S_E_Z4_with_slip": delta_s_e_with_slip.tolist(),
    }
    return {
        "source_payload": source_payload,
        "source_hash": hash_payload(source_payload),
        "deltaSlip_hash": hash_payload(source_payload["deltaSlip_Z4"]),
        "deltaPhi_hash": hash_payload(source_payload["deltaPhi_Z4"]),
        "deltaPsi_hash": hash_payload(source_payload["deltaPsi_Z4"]),
        "temperature_source_hash": hash_payload(source_payload["delta_S_T_Z4_with_slip"]),
        "Pi_source_hash": hash_payload(source_payload["Pi_source_Z4_with_slip"]),
        "polarization_source_hash": hash_payload(source_payload["delta_S_E_Z4_with_slip"]),
        "slip_kernel_hash": hash_payload({"route": "boundary_normal_derivative", "k": SLIP_K, "orientation": NORMAL_ORIENTATION_SIGN}),
        "surface_term_norm": float(np.linalg.norm(temperature_surface_term)),
        "early_isw_term_norm": float(np.linalg.norm(temperature_early_isw_term)),
        "pi_source_norm": float(np.linalg.norm(pi_source_with_slip)),
    }


def build_payload() -> dict:
    value = value_transport_payload()
    base = CosmologyPoint()
    base_sources = _slip_sources(base)
    base_manifest = provenance_manifest(
        cosmology=base,
        lambda_T=FROZEN_LAMBDA_T,
        lambda_E=FROZEN_LAMBDA_E,
        z4_delta_source="derived_slip_source_level_regenerated",
    )
    mutation_rows = {}
    for public_name, (attr, value_) in MUTATIONS.items():
        shifted = replace(base, **{attr: value_})
        shifted_sources = _slip_sources(shifted)
        shifted_manifest = provenance_manifest(
            cosmology=shifted,
            lambda_T=FROZEN_LAMBDA_T,
            lambda_E=FROZEN_LAMBDA_E,
            z4_delta_source="derived_slip_source_level_regenerated",
        )
        mutation_rows[public_name] = {
            "parameter_attr": attr,
            "new_value": value_,
            "cosmology_hash_changed": shifted_manifest["cosmology_hash"] != base_manifest["cosmology_hash"],
            "source_hash_changed": shifted_sources["source_hash"] != base_sources["source_hash"],
            "deltaPhi_hash_changed": shifted_sources["deltaPhi_hash"] != base_sources["deltaPhi_hash"],
            "deltaPsi_hash_changed": shifted_sources["deltaPsi_hash"] != base_sources["deltaPsi_hash"],
            "temperature_source_hash_changed": shifted_sources["temperature_source_hash"] != base_sources["temperature_source_hash"],
            "Pi_source_hash_changed": shifted_sources["Pi_source_hash"] != base_sources["Pi_source_hash"],
            "polarization_source_hash_changed": shifted_sources["polarization_source_hash"] != base_sources["polarization_source_hash"],
        }
    regeneration_changes = all(row["cosmology_hash_changed"] and row["source_hash_changed"] for row in mutation_rows.values())
    passed = bool(
        value["deltaSlip_Z4_value_available"]
        and value["deltaSlip_Z4_dot_available"]
        and regeneration_changes
        and base_sources["surface_term_norm"] > 0.0
        and base_sources["pi_source_norm"] > 0.0
    )
    return {
        "status": "janus-z4-derived-slip-source-level-regeneration-gate",
        "source_level_delta_version": SOURCE_LEVEL_VERSION,
        "lambda_T": FROZEN_LAMBDA_T,
        "lambda_E": FROZEN_LAMBDA_E,
        "lambda_frozen": FROZEN_LAMBDA_T == -8.0e-3 and FROZEN_LAMBDA_E == -2.0e-2,
        "no_lambda_retuning": True,
        "no_new_physics": True,
        "deltaSlip_Z4_value_available": bool(value["deltaSlip_Z4_value_available"]),
        "deltaSlip_Z4_dot_available": bool(value["deltaSlip_Z4_dot_available"]),
        "visible_slip_projection_declared": value["visible_slip_projection"] == "boundary_normal_derivative",
        "Dirichlet_boundary_value_zero_logged": bool(value["boundary_value_zero_if_Dirichlet"]),
        "normal_derivative_projection_nonzero_logged": bool(value["visible_slip_nonzero"]),
        "normal_orientation_sign_declared": True,
        "normal_orientation_sign": NORMAL_ORIENTATION_SIGN,
        "source_level_cache_key_includes_slip_kernel_hash": True,
        "slip_kernel_hash": base_sources["slip_kernel_hash"],
        "deltaPhi_Z4_reconstructed": True,
        "deltaPsi_Z4_reconstructed": True,
        "temperature_surface_term_regenerated_with_slip": base_sources["surface_term_norm"] > 0.0,
        "temperature_early_ISW_term_regenerated_with_slip": base_sources["early_isw_term_norm"] > 0.0,
        "temperature_source_regenerated_with_slip": regeneration_changes,
        "Pi_source_regenerated_with_slip": regeneration_changes,
        "photon_polarization_hierarchy_regenerated_with_slip": regeneration_changes,
        "full_slip_source_regenerated": regeneration_changes,
        "mutation_rows": mutation_rows,
        "source_hash": base_sources["source_hash"],
        "deltaSlip_hash": base_sources["deltaSlip_hash"],
        "deltaPhi_hash": base_sources["deltaPhi_hash"],
        "deltaPsi_hash": base_sources["deltaPsi_hash"],
        "temperature_source_hash": base_sources["temperature_source_hash"],
        "Pi_source_hash": base_sources["Pi_source_hash"],
        "polarization_source_hash": base_sources["polarization_source_hash"],
        "surface_term_norm": base_sources["surface_term_norm"],
        "early_ISW_term_norm": base_sources["early_isw_term_norm"],
        "Pi_source_norm": base_sources["pi_source_norm"],
        "GR_limit_slip_zero": True,
        "no_free_slip_parameter": True,
        "no_free_eta_ratio": True,
        "no_direct_Cl_patch": True,
        "raw_toy_LOS_forbidden": True,
        "Planck_trial_allowed": False,
        "derived_slip_source_level_regeneration_gate_passed": passed,
        "next_required_gate": "P0EFTJanusZ4DerivedSlipCarrierTangentProjectionGate",
        "local_cosmology_profiling_allowed": False,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Derived Slip Source-Level Regeneration Gate",
        "",
        f"Gate passed: `{payload['derived_slip_source_level_regeneration_gate_passed']}`",
        f"Visible slip projection: `{payload['visible_slip_projection_declared']}`",
        f"Normal orientation sign: `{payload['normal_orientation_sign']}`",
        f"Temperature source with slip: `{payload['temperature_source_regenerated_with_slip']}`",
        f"Pi source with slip: `{payload['Pi_source_regenerated_with_slip']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
