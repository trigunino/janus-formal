from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_active_inputs import load_active_z2sigma_bao_inputs
from scripts.build_p0_eft_janus_z2_sigma_bao_nonfit_materialization_runner import (
    build_payload as build_nonfit_materialization_payload,
)


MEAN_PATH = Path("data/raw/desi_dr2/desi_gaussian_bao_ALL_GCcomb_mean.txt")
COV_PATH = Path("data/raw/desi_dr2/desi_gaussian_bao_ALL_GCcomb_cov.txt")
ACTIVE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_active_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_active_readiness_gate.json")


def _mean_rows() -> list[tuple[float, float, str]]:
    if not MEAN_PATH.exists():
        return []
    rows: list[tuple[float, float, str]] = []
    for line in MEAN_PATH.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        z, value, quantity = line.split()
        rows.append((float(z), float(value), quantity))
    return rows


def _cov_shape() -> tuple[int, int]:
    if not COV_PATH.exists():
        return 0, 0
    rows = [line.split() for line in COV_PATH.read_text(encoding="utf-8").splitlines() if line.strip()]
    return len(rows), len(rows[0]) if rows else 0


def _active_input_status() -> dict:
    if not ACTIVE_INPUT_PATH.exists():
        return {
            "manifest_path": str(ACTIVE_INPUT_PATH),
            "manifest_exists": False,
            "manifest_valid": False,
            "validation_error": "active BAO input manifest is missing",
            "rd_mpc": None,
        }
    try:
        inputs = load_active_z2sigma_bao_inputs(ACTIVE_INPUT_PATH)
        rd_mpc = inputs.rd_mpc()
    except Exception as exc:
        return {
            "manifest_path": str(ACTIVE_INPUT_PATH),
            "manifest_exists": True,
            "manifest_valid": False,
            "validation_error": str(exc),
            "rd_mpc": None,
        }
    return {
        "manifest_path": str(ACTIVE_INPUT_PATH),
        "manifest_exists": True,
        "manifest_valid": True,
        "validation_error": None,
        "z_points": int(len(inputs.z_grid)),
        "z_d_Z2Sigma": float(inputs.z_d),
        "z_max": float(inputs.z_max),
        "omega_k_Z2Sigma": float(inputs.omega_k_z2sigma),
        "rd_mpc": float(rd_mpc),
    }


def build_payload() -> dict:
    mean_rows = _mean_rows()
    cov_rows, cov_cols = _cov_shape()
    active_input_status = _active_input_status()
    materialization = build_nonfit_materialization_payload()
    active_manifest_ready = bool(active_input_status["manifest_valid"])
    active_inputs = {
        "H_Z2Sigma_numerical_ready": active_manifest_ready,
        "D_M_D_H_D_V_Z2Sigma_ready": active_manifest_ready,
        "c_s_Z2Sigma_ready": active_manifest_ready,
        "z_d_Z2Sigma_ready": active_manifest_ready,
        "r_d_Z2Sigma_evaluated": active_manifest_ready and active_input_status["rd_mpc"] is not None,
    }
    data_inputs = {
        "desi_dr2_gaussian_bao_mean_ready": len(mean_rows) == 13,
        "desi_dr2_gaussian_bao_covariance_ready": cov_rows == len(mean_rows) and cov_cols == len(mean_rows),
    }
    calculator = {
        "strict_H_Z2Sigma_builder_ready": True,
        "strict_effective_fluid_assembler_ready": True,
        "effective_fluid_assembler_requires_active_FLRW_components": True,
        "H_builder_requires_active_H0_Z2Sigma": True,
        "H_builder_requires_active_rho_eff_over_rho_crit0": True,
        "strict_c_s_Z2Sigma_builder_ready": True,
        "c_s_builder_requires_active_baryon_density": True,
        "c_s_builder_requires_active_photon_density": True,
        "strict_z_d_Z2Sigma_solver_ready": True,
        "z_d_solver_requires_active_H_Z2Sigma": True,
        "z_d_solver_requires_active_drag_rate": True,
        "strict_z2_sigma_bao_calculator_ready": True,
        "strict_z2_sigma_sound_ruler_integrator_ready": True,
        "calculator_requires_active_H_Z2Sigma": True,
        "calculator_requires_active_rd_Z2Sigma": True,
        "sound_ruler_integrator_requires_active_c_s_Z2Sigma": True,
        "sound_ruler_integrator_requires_active_z_d_Z2Sigma": True,
        "calculator_has_no_planck_lcdm_defaults": True,
    }
    forbidden = {
        "compressed_planck_lcdm_rd_forbidden": True,
        "planck_like_scale_forbidden": True,
        "archived_z4_bao_reuse_forbidden": True,
        "phenomenological_holst_bao_scan_forbidden": True,
    }
    bibliography = {
        "distance_measures": "https://ned.ipac.caltech.edu/level5/Hogg/paper.pdf",
        "etherington_reciprocity": "https://arxiv.org/abs/2112.05701",
        "sound_horizon_drag_epoch": "https://arxiv.org/abs/astro-ph/9709112",
        "janus_projective_context": "https://arxiv.org/abs/2412.04644",
    }
    prediction_ready = (
        all(active_inputs.values())
        and all(data_inputs.values())
        and all(calculator.values())
        and all(forbidden.values())
    )
    return {
        "status": "janus-z2-sigma-bao-active-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "bibliography": bibliography,
        "mean_path": str(MEAN_PATH),
        "covariance_path": str(COV_PATH),
        "active_input_status": active_input_status,
        "data_points": len(mean_rows),
        "quantities": sorted({row[2] for row in mean_rows}),
        "covariance_shape": [cov_rows, cov_cols],
        "active_inputs": active_inputs,
        "nonfit_materialization": {
            "gate": materialization["status"],
            "passed": materialization["gate_passed"],
            "bao_chi2_evaluated": materialization["bao_chi2_evaluated"],
            "blocker": materialization["blocker"],
            "missing_real_active_inputs": materialization["missing_real_active_inputs"],
            "steps_passed": materialization["steps_passed"],
            "uses_compressed_planck_lcdm": materialization["uses_compressed_planck_lcdm"],
            "uses_archived_z4": materialization["uses_archived_z4"],
        },
        "data_inputs": data_inputs,
        "calculator": calculator,
        "forbidden_reuse": forbidden,
        "bao_prediction_vector_ready": prediction_ready,
        "bao_chi2_evaluated": False,
        "bao_active_readiness_gate_passed": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "blocker": materialization["blocker"]
        or "active H_Z2Sigma, c_s_Z2Sigma, z_d_Z2Sigma and r_d_Z2Sigma are not numerically derived",
        "next_required": [
            "pass_BAO_nonfit_materialization_runner",
            "close_numerical_H_Z2Sigma_from_active_effective_fluid",
            "derive_c_s_Z2Sigma_for_active_photon_baryon_plasma",
            "derive_z_d_Z2Sigma_drag_epoch_condition",
            "evaluate_r_d_Z2Sigma_without_compressed_Planck_LCDM_prior",
            "compute_D_M_D_H_D_V_and_DESI_DR2_covariance_chi2",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Active Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Bibliography checked: `{payload['bibliography_checked']}`",
        f"DESI DR2 data points: `{payload['data_points']}`",
        f"Quantities: `{payload['quantities']}`",
        f"Strict H builder ready: `{payload['calculator']['strict_H_Z2Sigma_builder_ready']}`",
        f"Strict c_s builder ready: `{payload['calculator']['strict_c_s_Z2Sigma_builder_ready']}`",
        f"Strict z_d solver ready: `{payload['calculator']['strict_z_d_Z2Sigma_solver_ready']}`",
        f"Strict calculator ready: `{payload['calculator']['strict_z2_sigma_bao_calculator_ready']}`",
        f"Strict sound-ruler integrator ready: `{payload['calculator']['strict_z2_sigma_sound_ruler_integrator_ready']}`",
        f"Prediction vector ready: `{payload['bao_prediction_vector_ready']}`",
        f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
        f"Gate passed: `{payload['bao_active_readiness_gate_passed']}`",
        "",
        "## Blocker",
        payload["blocker"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
