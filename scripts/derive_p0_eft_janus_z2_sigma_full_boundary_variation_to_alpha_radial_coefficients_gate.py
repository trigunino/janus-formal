from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_sigma_boundary_action_support_gate import (
    build_payload as build_support,
)
from scripts.build_p0_eft_janus_sigma_boundary_nonlinear_residual_closure_gate import (
    build_payload as build_nonlinear_closure,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate import (
    build_payload as build_boundary_functional,
)
from scripts.derive_p0_eft_janus_z2_sigma_cartan_ghy_junction_trace_partition_audit import (
    build_payload as build_cartan_partition,
)
from scripts.derive_p0_eft_janus_z2_sigma_rh_rk_trace_derivation_frontier_gate import (
    build_payload as build_trace_frontier,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_full_boundary_variation_to_alpha_radial_coefficients_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_full_boundary_variation_to_alpha_radial_coefficients_gate.json"
)
OUTPUT_CONTRACT = Path(
    "outputs/active_z2_sigma/counterterm_alpha_res_radial_components.json"
)


def build_payload() -> dict:
    support = build_support()
    nonlinear = build_nonlinear_closure()
    functional = build_boundary_functional()
    cartan = build_cartan_partition()
    frontier = build_trace_frontier()

    metric_extrinsic_values_available = bool(
        nonlinear["component_emission"]["R_h_ab_emitted"]
        and nonlinear["component_emission"]["R_K_ab_emitted"]
    )
    coefficient_expansion_ready = bool(
        functional["closure"]["explicit_coefficient_expansion_ready"]
    )
    linear_k_available_as_residual = not bool(cartan["linear_K_partition_closed"])
    radial_coefficients_ready = (
        metric_extrinsic_values_available
        or coefficient_expansion_ready
        or linear_k_available_as_residual
    )

    return {
        "status": "janus-z2-sigma-full-boundary-variation-to-alpha-radial-coefficients-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "symbolic_sigma_support_closed": bool(
            support["sigma_boundary_support_declared"]
            and support["full_boundary_action_closed_on_sigma"]
        ),
        "component_level_residual_values_available": metric_extrinsic_values_available,
        "explicit_L_ct_coefficient_expansion_ready": coefficient_expansion_ready,
        "linear_K_residual_available_after_Cartan_GHY_partition": linear_k_available_as_residual,
        "excluded_sources": {
            "Cartan_GHY_linear_K_trace": "already_partitioned_into_junction_not_counterterm",
            "minimal_density_basis": "cannot_determine_coefficients_without_trace_or_boundary_condition",
            "symbolic_S_ct_functional": "declares_primitive_but_not_metric_extrinsic_values",
            "Z2_oddness_of_L_ct": "requires_alpha_res_components_before_it_can_prove_E_counterterm_zero",
        },
        "radial_decomposition_formula": {
            "alpha_h_radial": "sqrt_abs_h * 2 * R_Sigma * R_h_trace",
            "alpha_K_radial": "sqrt_abs_h * R_K_trace",
            "round_throat_metric_variation": "h_ab = R_Sigma^2 q_ab",
        },
        "required_output_contract": {
            "path": str(OUTPUT_CONTRACT),
            "fields": [
                "active_core",
                "source",
                "a_grid",
                "R_Sigma_values",
                "sqrt_abs_h_values",
                "alpha_h_radial_coefficient_values",
                "alpha_K_radial_coefficient_values",
            ],
        },
        "downstream_frontier_primary_blocker": frontier["primary_blocker"],
        "counterterm_alpha_res_radial_components_ready": radial_coefficients_ready,
        "gate_passed": radial_coefficients_ready,
        "primary_blocker": (
            "none"
            if radial_coefficients_ready
            else "explicit_full_sigma_boundary_variation_metric_extrinsic_residual_values"
        ),
        "next_required": []
        if radial_coefficients_ready
        else [
            "derive_R_h_trace_or_alpha_h_radial_from_delta_Sigma_boundary_action_delta_RSigma",
            "derive_R_K_trace_or_alpha_K_radial_from_delta_Sigma_boundary_action_delta_RSigma",
            "write_counterterm_alpha_res_radial_components_json",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Full Boundary Variation to Alpha Radial Coefficients Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"Symbolic Sigma support closed: `{payload['symbolic_sigma_support_closed']}`",
        f"Component residual values available: `{payload['component_level_residual_values_available']}`",
        "",
        "## Excluded Sources",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["excluded_sources"].items())
    lines.extend(["", "## Required Output Contract"])
    lines.extend(f"- `{field}`" for field in payload["required_output_contract"]["fields"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
