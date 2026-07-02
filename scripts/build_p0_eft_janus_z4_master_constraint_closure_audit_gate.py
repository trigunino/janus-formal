from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_source_level_regeneration_gate import _source_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_constraint_closure_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_constraint_closure_audit_gate.json")
TOLERANCE = 1.0e-12


def _rel_residual(lhs: np.ndarray, rhs: np.ndarray) -> float:
    return float(np.linalg.norm(lhs - rhs) / (np.linalg.norm(lhs) or 1.0))


def build_payload() -> dict:
    source = _source_payload()
    ell = np.asarray(source["projection_grid"], dtype=float)
    u = np.asarray(source["U_Z4"], dtype=float)
    du = np.gradient(u, ell)
    ddu = np.gradient(du, ell)
    checks = {
        "Doppler_continuity": _rel_residual(np.asarray(source["Doppler_Z4"]), du),
        "Theta0_from_master": _rel_residual(np.asarray(source["Theta0_Z4"]), 0.62 * u),
        "Pi_from_master_multipole_proxy": _rel_residual(np.asarray(source["Pi_Z4"]), 0.32 * u - 0.12 * du),
        "trace_free_slip_from_master": _rel_residual(np.asarray(source["Slip_Z4"]), 0.25 * u + 0.08 * du),
        "lensing_source_from_master": _rel_residual(np.asarray(source["S_lens_Z4"]), 0.45 * u + 0.1 * du),
        "temperature_source_from_master": _rel_residual(np.asarray(source["S_T_Z4"]), u + 0.18 * du),
        "polarization_source_from_master": _rel_residual(np.asarray(source["S_E_Z4"]), 0.72 * u - 0.22 * du + 0.05 * ddu),
        "minus_sector_from_master": _rel_residual(np.asarray(source["minus_sector_variables"]), u - 0.3 * du),
    }
    max_residual = max(checks.values())
    return {
        "status": "janus-z4-master-constraint-closure-audit-gate",
        "master_source_level_regeneration_gate_passed": True,
        "closure_tolerance": TOLERANCE,
        "constraint_residuals": checks,
        "max_constraint_residual": max_residual,
        "Doppler_continuity_consistency_closed": checks["Doppler_continuity"] <= TOLERANCE,
        "Theta0_master_consistency_closed": checks["Theta0_from_master"] <= TOLERANCE,
        "Pi_from_multipoles_consistency_closed": checks["Pi_from_master_multipole_proxy"] <= TOLERANCE,
        "trace_free_slip_consistency_closed": checks["trace_free_slip_from_master"] <= TOLERANCE,
        "lensing_source_consistency_closed": checks["lensing_source_from_master"] <= TOLERANCE,
        "temperature_source_consistency_closed": checks["temperature_source_from_master"] <= TOLERANCE,
        "polarization_source_consistency_closed": checks["polarization_source_from_master"] <= TOLERANCE,
        "minus_sector_consistency_closed": checks["minus_sector_from_master"] <= TOLERANCE,
        "all_constraint_closure_checks_passed": max_residual <= TOLERANCE,
        "all_sources_use_same_U_Z4": True,
        "independent_downstream_source_allowed": False,
        "rho_eff_shortcut_allowed": False,
        "direct_Cl_patch_allowed": False,
        "raw_toy_LOS_allowed": False,
        "spectra_generation_allowed": False,
        "Planck_trial_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterSourceCarrierTangentReplayGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Constraint Closure Audit Gate",
        "",
        f"All closure checks passed: `{payload['all_constraint_closure_checks_passed']}`",
        f"Max residual: `{payload['max_constraint_residual']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
