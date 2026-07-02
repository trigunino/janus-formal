from __future__ import annotations

import json
import sys
from dataclasses import asdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
    sys.path.insert(0, str(ROOT / "src"))

from janus_lab.z4_cmb_solver import Z4CMBSolverSettings, params_from_cosmology
from janus_lab.z4_regenerative_camb_provider import CosmologyPoint
from scripts.build_p0_eft_janus_z4_complete_cl_convention_calibration_gate import build_payload as calibration_payload
from scripts.build_p0_eft_janus_z4_complete_gr_limit_shape_gate import build_payload as gr_limit_payload

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_solver_input_manifest_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_solver_input_manifest_gate.json")


def _z4_manifest() -> dict:
    cosmology = CosmologyPoint()
    settings = Z4CMBSolverSettings(z4_enabled=True)
    params = params_from_cosmology(cosmology, settings)
    return {
        "z4_enabled": settings.z4_enabled,
        "sector_minus_enabled": params.omega_minus != 0.0,
        "torsion_enabled": "unspecified",
        "projection_type": "plus_sector_with_projection_minus_weight",
        "projection_minus_weight": params.projection_minus_weight,
        "cross_coupling": params.cross_coupling,
        "gravitational_sign_policy": "implicit_in_sector_potentials",
        "thermodynamic_density_sign_policy": "not_declared_in_solver_manifest",
        "boundary_conditions": "not_declared",
        "master_variable": "not_declared",
        "initial_mode": "hardcoded_plus_adiabatic_with_fixed_minus_seed",
        "minus_initial_seed": -2.0e-6,
        "minus_microphysics": "not_declared",
        "slip_policy": "zero_except_pi_nu_default",
        "normalization_policy": "proxy_amplitude_then_channel_calibration",
    }


def build_payload() -> dict:
    cosmology = CosmologyPoint()
    settings = Z4CMBSolverSettings()
    calibration = calibration_payload()
    gr_limit = gr_limit_payload()
    z4 = _z4_manifest()
    hidden_default_inputs = bool(
        z4["boundary_conditions"] == "not_declared"
        or z4["master_variable"] == "not_declared"
        or z4["minus_microphysics"] == "not_declared"
        or z4["thermodynamic_density_sign_policy"] == "not_declared_in_solver_manifest"
    )
    global_ls_calibration = calibration.get("channel_scales_finite", False) and calibration.get("cl_convention_calibration_passed", False)
    z4_initial_mode_unspecified = z4["initial_mode"].startswith("hardcoded")
    projection_unspecified = z4["projection_type"] == "not_declared"
    minus_microphysics_unspecified = z4["minus_microphysics"] == "not_declared"
    conventions_known = bool(gr_limit["gr_limit_shape_passed"])
    blockers = {
        "hidden_default_inputs": hidden_default_inputs,
        "fixed_csv_theory": False,
        "global_LS_channel_calibration": global_ls_calibration,
        "z4_initial_mode_unspecified": z4_initial_mode_unspecified,
        "projection_unspecified": projection_unspecified,
        "minus_microphysics_unspecified": minus_microphysics_unspecified,
        "Cl_or_Cphi_convention_unknown": not conventions_known,
    }
    passed = not any(blockers.values())
    return {
        "status": "janus-z4-solver-input-manifest-gate",
        "backend": "complete_z4_solver_with_camb_gr_anchor",
        "cosmology": asdict(cosmology),
        "primordial": {
            "P_R_type": "power_law",
            "A_s": cosmology.As,
            "n_s": cosmology.ns,
            "pivot": "implicit_CAMB_default",
        },
        "recombination": {
            "gr_limit_source": "regenerative_CAMB_GR_anchor",
            "z4_on_source": "internal_visibility_proxy",
            "modified_by_Z4": False,
        },
        "z4_inputs": z4,
        "numerics": {
            "k_grid": list(settings.k_values),
            "ell_values": list(settings.ell_values),
            "steps": settings.steps,
            "x_initial": settings.x_initial,
            "x_final": settings.x_final,
            "lensed": True,
        },
        "conventions": {
            "Cl_convention": "C_l",
            "C_phi_phi_convention": "C_L_phiphi",
            "units": "dimensionless_Cl_after_GR_anchor",
            "gr_limit_shape_passed": gr_limit["gr_limit_shape_passed"],
        },
        "calibration": {
            "unit_conversion_only": False,
            "global_shape_rescale": True,
            "LS_channel_scale": "present_in_complete_cl_convention_calibration_gate",
            "calibration_is_physical_validation": False,
        },
        "blockers": blockers,
        "solver_input_manifest_passed": passed,
        "z4_observed_planck_interpretation_allowed": passed,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "replace_LS_channel_calibration_and_declare_Z4_physical_inputs" if not passed else "z4_on_observed_diagnostic",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Solver Input Manifest Gate",
        "",
        f"Manifest passed: `{payload['solver_input_manifest_passed']}`",
        f"Z4 observed Planck interpretation allowed: `{payload['z4_observed_planck_interpretation_allowed']}`",
        "",
        "## Blockers",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["blockers"].items())
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
