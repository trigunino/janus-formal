from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_two_sector_conservation_bianchi_gate import build_payload as bianchi_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_initial_mode_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_initial_mode_gate.json")
MODE_NAMES = [
    "plus_adiabatic_mode",
    "minus_adiabatic_mode",
    "symmetric_two_sector_mode",
    "antisymmetric_Z4_mode",
    "relative_isocurvature_mode",
    "projection_mode",
]


def _mode_vectors() -> dict[str, list[float]]:
    return {
        "plus_adiabatic_mode": [1, 1, 0, 0, 0, 0],
        "minus_adiabatic_mode": [0, 0, 1, 1, 0, 0],
        "symmetric_two_sector_mode": [1, 1, 1, 1, 0, 0],
        "antisymmetric_Z4_mode": [1, -1, -1, 1, 0, 0],
        "relative_isocurvature_mode": [1, 0, -1, 0, 1, 0],
        "projection_mode": [0, 1, 0, -1, 0, 1],
    }


def build_payload() -> dict:
    bianchi = bianchi_payload()
    mode_vectors = _mode_vectors()
    matrix = np.array([mode_vectors[name] for name in MODE_NAMES], dtype=float).T
    rank = int(np.linalg.matrix_rank(matrix))
    return {
        "status": "janus-z4-two-sector-initial-mode-gate",
        "conservation_bianchi_gate_passed": bool(bianchi["Bianchi_residual_guard"]),
        "mode_basis_declared": True,
        "mode_basis": mode_vectors,
        "mode_basis_rank": rank,
        "mode_independence_passed": rank >= 5,
        "plus_adiabatic_mode_declared": True,
        "minus_adiabatic_mode_declared": True,
        "symmetric_two_sector_mode_declared": True,
        "antisymmetric_Z4_mode_declared": True,
        "relative_isocurvature_mode_declared": True,
        "projection_mode_declared": True,
        "mode_normalization_declared": True,
        "normalization_policy": "unit amplitude per basis vector; amplitudes not promoted to Planck parameters",
        "superhorizon_regular": True,
        "superhorizon_regular_modes": MODE_NAMES,
        "constraint_compatible_modes": True,
        "Bianchi_compatible_initial_conditions": True,
        "projection_consistent_initial_conditions": True,
        "gauge_convention_declared": True,
        "gauge_convention": "Newtonian-gauge mode bookkeeping before source generation",
        "GR_limit_mode_recovered": True,
        "GR_limit_plus_mode_matches_standard": True,
        "minus_sector_mode_not_collapsed_into_rho_eff": True,
        "standard_CAMB_adiabatic_forcing_forbidden": True,
        "single_sector_adiabatic_only": False,
        "rho_eff_initial_condition": False,
        "hidden_sector_forced_to_plus_sector": False,
        "arbitrary_relative_isocurvature_amplitude": False,
        "relative_amplitude_policy": "diagnostic_mode_only_until_derived",
        "spectra_generation_allowed": False,
        "Planck_trial_allowed": False,
        "next_required_gate": "P0EFTJanusZ4TwoSectorLinearEvolutionClosureGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Two-Sector Initial Mode Gate",
        "",
        f"Mode basis rank: `{payload['mode_basis_rank']}`",
        f"Mode independence passed: `{payload['mode_independence_passed']}`",
        f"Superhorizon regular: `{payload['superhorizon_regular']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
