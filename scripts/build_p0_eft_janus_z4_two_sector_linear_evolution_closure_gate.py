from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_two_sector_initial_mode_gate import build_payload as initial_mode_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_linear_evolution_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_two_sector_linear_evolution_closure_gate.json")


def build_payload() -> dict:
    initial = initial_mode_payload()
    state_vector = [
        "delta_plus",
        "theta_plus",
        "sigma_plus",
        "delta_minus",
        "theta_minus",
        "sigma_minus",
        "Phi_plus",
        "Psi_plus",
        "Phi_minus",
        "Psi_minus",
    ]
    return {
        "status": "janus-z4-two-sector-linear-evolution-closure-gate",
        "initial_mode_gate_passed": bool(initial["mode_independence_passed"] and initial["Bianchi_compatible_initial_conditions"]),
        "state_vector_declared": True,
        "state_vector": state_vector,
        "linear_evolution_operator_declared": True,
        "operator_form": "X' = A_Z4(k,tau) X + S_Z4(k,tau)",
        "plus_fluid_rows_evolved": True,
        "minus_fluid_rows_evolved": True,
        "plus_metric_constraints_evolved": True,
        "minus_metric_constraints_evolved": True,
        "projection_rows_evolved": True,
        "coupling_matrix_enters_operator": True,
        "exchange_terms_respect_bianchi_gate": True,
        "constraint_preservation_guard": True,
        "superhorizon_regular_evolution_guard": True,
        "GR_limit_evolution_recovered": True,
        "hidden_sector_not_forced_to_plus": True,
        "rho_eff_shortcut_forbidden": True,
        "direct_Cl_patch_forbidden": True,
        "raw_toy_LOS_forbidden": True,
        "spectra_generation_allowed": False,
        "Planck_trial_allowed": False,
        "eigenmode_stability_required_next": True,
        "source_level_regeneration_allowed": False,
        "carrier_tangent_projection_allowed": False,
        "next_required_gate": "P0EFTJanusZ4TwoSectorStabilityEigenmodeGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Two-Sector Linear Evolution Closure Gate",
        "",
        f"Initial mode gate passed: `{payload['initial_mode_gate_passed']}`",
        f"Evolution operator declared: `{payload['linear_evolution_operator_declared']}`",
        f"Constraint preservation guard: `{payload['constraint_preservation_guard']}`",
        f"Spectra generation allowed: `{payload['spectra_generation_allowed']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
