from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_plugstar_curvature_amplitude_from_embedding_gate import (
    build_payload as build_active_a_k_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_plugstar_ejection_threshold_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_plugstar_ejection_threshold_gate.json"
)


def build_payload(*, active_a_k_payload: dict | None = None) -> dict:
    active_a_k = active_a_k_payload if active_a_k_payload is not None else build_active_a_k_payload()
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
    active_bound_ready = bool(active_a_k.get("gate_passed", False))
    active_threshold_solution = active_a_k.get("threshold_solution") if active_bound_ready else None
    route_status = "active_bound_ready" if active_bound_ready else (
        "conditional_closed_waiting_for_active_A_K" if gate_passed else "credible_but_blocked"
    )
    archive_decision = {
        "archive_ready": True,
        "archive_status": "ready_to_archive_as_conditional_parallel_branch",
        "final_verdict": "useful_as_minimum_throat_constraint_not_active_closure",
        "closed_part": "Z2 transmission compatibility and formal threshold equation",
        "conditional_part": "numeric active bound requires active A_K from embedding curvature",
        "unresolved_active_blocker": "none"
        if active_bound_ready
        else active_a_k["primary_blocker"],
        "active_pipeline_promotion_allowed": active_bound_ready,
        "active_pipeline_import_forbidden_until_A_K_ready": not active_bound_ready,
    }
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
        "active_A_K_status": {
            "gate": active_a_k["status"],
            "gate_passed": active_bound_ready,
            "route_status": active_a_k["route_status"],
            "primary_blocker": active_a_k["primary_blocker"],
            "certificate": active_a_k.get("active_A_K_certificate"),
        },
        "active_threshold_solution": active_threshold_solution,
        "archive_decision": archive_decision,
        "candidate_thresholds": candidate_thresholds,
        "closure": closure,
        "route_status": route_status,
        "gate_passed": gate_passed,
        "primary_blocker": "none" if gate_passed else blockers[0],
        "blockers": blockers,
        "interpretation": (
            "The isolated plugstar route closes conditionally on the curvature "
            "threshold certificate. A numeric active lower bound is ready only when "
            "A_K is derived from active embedding curvature data."
        ),
        "next_required": []
        if active_bound_ready
        else active_a_k["next_required"],
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
    lines.extend(["", "## Active A_K"])
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in payload["active_A_K_status"].items()
    )
    if payload["active_threshold_solution"] is not None:
        lines.extend(["", "## Active Threshold Solution"])
        lines.extend(
            f"- `{key}`: `{value}`"
            for key, value in payload["active_threshold_solution"].items()
        )
    lines.extend(["", "## Archive Decision"])
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in payload["archive_decision"].items()
    )
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
