from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate import (
    build_payload as build_residual_channel_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate import (
    build_payload as build_tetrad_residual_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_symbolic_local_primitive_gate import (
    build_payload as build_symbolic_primitive_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate import (
    build_payload as build_throat_radius_frontier_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_attack_order_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_attack_order_gate.json")


def build_payload() -> dict:
    residual_frontier = build_residual_channel_frontier_payload()
    tetrad = build_tetrad_residual_payload()
    symbolic = build_symbolic_primitive_payload()
    embedding = build_active_embedding_payload()
    throat = build_throat_radius_frontier_payload()

    nearest = residual_frontier["nearest_residual_channel_frontier"]
    active_embedding_ready = embedding["active_embedding_readiness_ready"]
    throat_radius_ready = throat["status_flags"]["R_Sigma_of_a_ready"]
    tetrad_ready = tetrad["counterterm_tetrad_residual_channel_ready"]
    symbolic_ready = symbolic["symbolic_local_primitive_ready"]
    coefficient_expansion_ready = symbolic["closure"]["coefficient_expansion_explicit"]

    declared = {
        "residual_channel_frontier_imported": True,
        "tetrad_residual_channel_imported": True,
        "active_embedding_readiness_imported": True,
        "throat_radius_solution_frontier_imported": True,
        "attack_order_is_diagnostic_only": True,
        "circular_radius_counterterm_dependency_checked": True,
        "lct_profile_currently_requires_radius_values": True,
        "non_circular_trace_route_required": True,
        "symbolic_local_counterterm_route_declared": True,
        "no_counterterm_channel_dropped": True,
        "no_fit_shortcut": True,
        "no_legacy_z4_import": True,
    }
    circular_dependency_detected = (
        not throat_radius_ready
        and not active_embedding_ready
        and not tetrad_ready
        and throat["status_flags"]["matter_flux_block_reduced"]
        and not throat["status_flags"]["counterterm_block_reduced"]
    )
    closure = {
        "nearest_channel_identified": nearest["channel"] == "tetrad",
        "tetrad_channel_is_nearest_not_ready": nearest["channel"] == "tetrad" and not tetrad_ready,
        "radius_counterterm_circular_dependency_detected": circular_dependency_detected,
        "active_embedding_ready": active_embedding_ready,
        "R_Sigma_solution_certificate_ready": throat_radius_ready,
        "symbolic_local_counterterm_route_ready": symbolic_ready,
        "counterterm_coefficient_expansion_explicit": coefficient_expansion_ready,
        "radial_profile_from_residual_contractions_non_circular": False,
        "trace_values_from_full_sigma_action_ready": False,
        "counterterm_attack_order_ready": False,
    }
    if not symbolic_ready:
        upstream_blocker = "symbolic_local_counterterm_route"
    elif not coefficient_expansion_ready:
        upstream_blocker = "active_boundary_variational_trace_values"
    elif not active_embedding_ready:
        upstream_blocker = "active_embedding_readiness"
    else:
        upstream_blocker = "tetrad_residual_channel"
    return {
        "status": "janus-z2-sigma-counterterm-attack-order-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": declared,
        "closure": closure,
        "attack_order": [
            "derive_counterterm_residual_symbolically_in_local_boundary_basis",
            "reduce_round_throat_tensor_residuals_to_R_h_trace_and_R_K_trace",
            "derive_boundary_variational_ensemble_Dirichlet_h_or_mixed_hK",
            "derive_R_h_trace_and_R_K_trace_from_full_Sigma_action_without_R_Sigma_certificate",
            "derive_counterterm_trace_residual_inputs_json",
            "materialize_R_h_ab_R_K_ab_from_trace_inputs",
            "only_then_integrate_L_ct_profile_or_replace_by_symbolic_R_dependent_profile",
            "derive_counterterm_residual_scalar_contractions_inputs",
            "write_counterterm_lct_radial_profile_from_residual_contractions",
            "reduce_E_counterterm_radial_block",
            "then_solve_R_Sigma_solution_certificate",
            "then_materialize_active_embedding_geometry",
            "then_evaluate_deltaK_and_torsion_pullback_on_embedding",
            "then_close_remaining_connection_embedding_matter_flux_channels",
            "then_form_exact_residual_one_form_and_counterterm_primitive",
        ],
        "upstream_frontiers": {
            "residual_channel_frontier": {
                "gate": residual_frontier["status"],
                "ready": residual_frontier["residual_channel_frontier_ready"],
                "nearest": nearest,
            },
            "tetrad_residual_channel": {
                "gate": tetrad["status"],
                "ready": tetrad_ready,
                "current_frontier": tetrad["current_frontier"],
            },
            "symbolic_local_primitive": {
                "gate": symbolic["status"],
                "ready": symbolic_ready,
                "closure": symbolic["closure"],
                "output_manifest": symbolic["output_manifest"],
            },
            "active_embedding": {
                "gate": embedding["status"],
                "ready": active_embedding_ready,
                "still_open": embedding["still_open"],
                "nearest": embedding["nearest_embedding_frontier"],
            },
            "throat_radius_solution": {
                "gate": throat["status"],
                "R_Sigma_of_a_ready": throat_radius_ready,
                "current_frontier": throat["current_frontier"],
                "nearest_radial_block_frontier": throat["nearest_radial_block_frontier"],
            },
        },
        "primary_blocker": upstream_blocker,
        "gate_passed": all(declared.values()) and all(closure.values()),
        "next_required": [
            "choose_and_derive_active_boundary_variational_ensemble",
            "derive_R_h_trace_and_R_K_trace_from_active_sigma_boundary_variation",
            "avoid_counterterm_lct_radial_profile_until_trace_values_are_non_circular",
            "write_counterterm_trace_residual_inputs_json",
            "prove_explicit_coefficients_preserve_L_ct_cancellation",
            "materialize_counterterm_residual_scalar_contractions_inputs",
            "run_counterterm_lct_radial_profile_from_residual_contractions",
            "rerun_counterterm_radial_reduction_frontier_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Attack Order Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Attack Order",
    ]
    lines.extend(f"- `{item}`" for item in payload["attack_order"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
