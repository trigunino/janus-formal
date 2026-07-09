from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_doppler_transport_closure_refinement_gate import build_payload as refinement_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_weak_surface_branch_diagnostic_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_weak_surface_branch_diagnostic_closure_gate.json")


def build_payload() -> dict:
    refinement = refinement_payload()
    closure = refinement["parallel_fraction_full_surface_refined"] >= 0.70
    return {
        "status": "janus-z4-weak-surface-branch-diagnostic-closure-gate",
        "SW_surface_orthogonal_component_exists": refinement["parallel_fraction_SW_only"] < 0.50,
        "SW_surface_parallel_fraction": refinement["parallel_fraction_SW_only"],
        "physical_Doppler_completed_surface_parallel_fraction": refinement["parallel_fraction_full_surface_refined"],
        "Doppler_completion_reintroduces_carrier_tangency": refinement["parallel_fraction_Doppler_refined"] >= 0.70,
        "surface_branch_status_before_closure": refinement["branch_status"],
        "close_weak_surface_branch": closure,
        "candidate_promotion_allowed": False,
        "Planck_trial_allowed": False,
        "diagnostic_surface_trial_allowed": False,
        "no_lambda_retuning": True,
        "no_free_Doppler_amplitude": True,
        "no_free_slip_parameter": True,
        "no_free_eta_ratio": True,
        "no_direct_Cl_patch": True,
        "raw_toy_LOS_forbidden": True,
        "next_recommended_channel": "two-sector Boltzmann dynamics or normal-mode bimetric slip transport",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Weak Surface Branch Diagnostic Closure Gate",
        "",
        f"Close weak surface branch: `{payload['close_weak_surface_branch']}`",
        f"SW surface parallel: `{payload['SW_surface_parallel_fraction']}`",
        f"Physical Doppler-completed parallel: `{payload['physical_Doppler_completed_surface_parallel_fraction']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
