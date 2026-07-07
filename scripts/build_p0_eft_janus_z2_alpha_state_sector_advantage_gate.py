from __future__ import annotations

import json
from pathlib import Path


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_state_sector_advantage_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_state_sector_advantage_gate.md")


def build_payload(*, require_physical_predictive_advantage: bool = False) -> dict:
    methodological_advantages = {
        "explicit_alpha_state_schema": True,
        "observational_fit_forbidden_in_state_input": True,
        "legacy_z4_reuse_forbidden": True,
        "full_no_fit_claim_forbidden": True,
        "failed_selector_routes_indexed": True,
        "conditional_pipeline_to_energy_and_density": True,
    }
    physical_predictive_advantage = False
    proceed = all(methodological_advantages.values()) and (
        physical_predictive_advantage or not require_physical_predictive_advantage
    )
    return {
        "status": "janus-z2-alpha-state-sector-advantage-gate",
        "active_core": "Z2_tunnel_Sigma",
        "published_janus_baseline": {
            "alpha_role": "exact_solution_integration_constant_or_scale_sector",
            "topology_predicts_alpha": False,
            "observational_calibration_can_select_sector": True,
        },
        "our_branch": {
            "alpha_role": "explicit_state_sector",
            "topology_predicts_alpha": False,
            "full_no_fit_prediction_ready": False,
            "methodological_advantages": methodological_advantages,
        },
        "physical_predictive_advantage_over_published_janus": physical_predictive_advantage,
        "methodological_pipeline_advantage_over_published_janus": all(
            methodological_advantages.values()
        ),
        "proceed_with_alpha_state_sector": proceed,
        "allowed_claim": (
            "This branch is not more predictive than published Janus on alpha. "
            "Its advantage is a stricter state-sector ledger: alpha may be used "
            "only with explicit provenance, no hidden observational fit, no Z4 "
            "reuse, and no full no-fit promotion."
        ),
        "forbidden_claims": [
            "alpha_predicted_by_Z2_topology",
            "alpha_predicted_by_Sigma_throat_without_state",
            "full_no_fit_cosmology_from_alpha_state_sector",
            "physical_predictive_advantage_over_published_Janus",
        ],
        "next_input_if_used": "outputs/active_z2_sigma/exact_solution_alpha_state_sector_inputs.json",
        "gate_passed": proceed,
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Alpha State-Sector Advantage Gate",
                "",
                f"Physical predictive advantage: `{payload['physical_predictive_advantage_over_published_janus']}`",
                f"Methodological pipeline advantage: `{payload['methodological_pipeline_advantage_over_published_janus']}`",
                f"Proceed with alpha state sector: `{payload['proceed_with_alpha_state_sector']}`",
                "",
                payload["allowed_claim"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
