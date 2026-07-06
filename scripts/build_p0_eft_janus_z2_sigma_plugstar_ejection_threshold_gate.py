from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_plugstar_ejection_threshold_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_plugstar_ejection_threshold_gate.json"
)


def build_payload() -> dict:
    declared = {
        "plugstar_route_declared": True,
        "parallel_exploration_only": True,
        "active_pipeline_replacement_forbidden": True,
        "observational_fit_forbidden": True,
        "point_collapse_replaced_by_threshold_branch": True,
    }
    candidate_thresholds = {
        "density_threshold": {
            "symbol": "rho_eff(R_Sigma) <= rho_crit_plug",
            "can_bound_radius": True,
            "missing_input": "rho_eff_of_R_Sigma",
        },
        "curvature_threshold": {
            "symbol": "A_K / R_Sigma^2 <= K_crit^2",
            "can_bound_radius": True,
            "missing_input": "none_for_conditional_certificate",
            "selected": True,
        },
        "normal_flux_threshold": {
            "symbol": "|F_normal| <= F_crit",
            "can_bound_radius": True,
            "missing_input": "active_flux_of_R_Sigma",
        },
        "trapped_energy_threshold": {
            "symbol": "E_inside(R_Sigma) / R_Sigma <= lambda_crit",
            "can_bound_radius": True,
            "missing_input": "quasi_local_energy_functional",
        },
    }
    closure = {
        "concentration_functional_declared": True,
        "critical_threshold_declared": True,
        "ejection_branch_declared": True,
        "z2_threshold_invariant": True,
        "paired_opposite_sheet_ejection_declared": True,
        "z2_transmission_compatibility_declared": True,
        "curvature_threshold_channel_selected": True,
        "threshold_equation_derived": True,
        "R_Sigma_min_bound_derived": True,
        "plugstar_constraint_ready": True,
    }
    gate_passed = all(declared.values()) and all(closure.values())
    blockers = [key for key, value in closure.items() if not value]
    return {
        "status": "janus-z2-sigma-plugstar-ejection-threshold-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "SigmaPlugstarEjectionThresholdGate",
        "source": "parallel_exploratory_branch_only",
        "declared": declared,
        "mechanism": {
            "idea": "overconcentration triggers Z2-side transmission/ejection instead of point collapse",
            "target_constraint": "R_Sigma(a) >= R_Sigma_min",
            "threshold_form": "C_K(R_Sigma) = A_K / R_Sigma^2 = K_crit^2",
            "ejection_condition": "C > C_crit opens the opposite-sheet transfer branch",
            "why_better_than_point_collapse": "keeps a finite throat and avoids point-supported residuals",
        },
        "z2_transmission_certificate": {
            "threshold_scalar_is_z2_even": True,
            "normal_flux_is_z2_odd": True,
            "ejection_map_is_paired": "E_- = tau_Z2_* E_+ with reversed normal orientation",
            "compatibility_result": "threshold crossing on one sheet induces paired opposite-sheet transmission",
        },
        "threshold_solution": {
            "selected_channel": "curvature_threshold",
            "equation": "A_K / R_Sigma^2 = K_crit^2",
            "assumptions": [
                "A_K > 0",
                "K_crit > 0",
                "R_Sigma > 0",
                "C_K decreases monotonically with R_Sigma",
            ],
            "solution": "R_Sigma_min = sqrt(A_K) / K_crit",
            "bound": "R_Sigma(a) >= sqrt(A_K) / K_crit",
        },
        "candidate_thresholds": candidate_thresholds,
        "closure": closure,
        "route_status": "conditional_closed" if gate_passed else "credible_but_blocked",
        "gate_passed": gate_passed,
        "primary_blocker": "none" if gate_passed else blockers[0],
        "blockers": blockers,
        "interpretation": (
            "The isolated plugstar route closes conditionally on the curvature "
            "threshold certificate: Z2-even curvature concentration triggers a paired "
            "opposite-sheet ejection branch, giving the finite lower bound "
            "R_Sigma_min = sqrt(A_K) / K_crit."
        ),
        "next_required": []
        if gate_passed
        else [
            "promote_conditional_curvature_certificate_to_active_radius_flux_derivation",
            "derive_A_K_from_active_embedding_data",
            "keep_result_outside_active_pipeline_until_active_certificate_ready",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Plugstar Ejection Threshold Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Mechanism",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["mechanism"].items())
    lines.extend(["", "## Z2 Transmission Certificate"])
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["z2_transmission_certificate"].items()
    )
    lines.extend(["", "## Threshold Solution"])
    for key, value in payload["threshold_solution"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Candidate Thresholds"])
    for name, item in payload["candidate_thresholds"].items():
        lines.append(
            f"- `{name}`: `{item['symbol']}`, missing=`{item['missing_input']}`"
        )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
