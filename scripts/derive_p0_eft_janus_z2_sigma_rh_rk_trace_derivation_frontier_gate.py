from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_resolved_throat_boundary_trace_targets_gate import (
    build_payload as build_trace_targets,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_basis_dual_route_decision_gate import (
    build_payload as build_minimal_dual_route,
)
from scripts.derive_p0_eft_janus_z2_sigma_alpha_radial_components_to_trace_residual_inputs_gate import (
    build_payload as build_alpha_to_trace,
)
from scripts.derive_p0_eft_janus_z2_sigma_alpha_res_metric_extrinsic_emission_contract_gate import (
    build_payload as build_emission_contract,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rh_rk_trace_derivation_frontier_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rh_rk_trace_derivation_frontier_gate.json"
)


def build_payload() -> dict:
    targets = build_trace_targets()
    minimal = build_minimal_dual_route()
    alpha_to_trace = build_alpha_to_trace()
    emission = build_emission_contract()
    trace_targets_ready = bool(
        targets["trace_targets"]["R_h_trace_derived"]
        and targets["trace_targets"]["R_K_trace_derived"]
    )
    alpha_radial_ready = bool(alpha_to_trace["gate_passed"])
    tensor_emission_ready = bool(emission["gate_passed"])
    ready = trace_targets_ready and alpha_radial_ready and tensor_emission_ready
    return {
        "status": "janus-z2-sigma-rh-rk-trace-derivation-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "frontier": {
            "trace_targets_declared": True,
            "trace_targets_derived": trace_targets_ready,
            "minimal_basis_can_derive_traces": minimal["routes"]["active_trace_solution_route"]["ready"],
            "alpha_radial_to_trace_conversion_ready": alpha_radial_ready,
            "trace_to_tensor_emission_ready": tensor_emission_ready,
        },
        "route_order": [
            "derive_alpha_h_radial_coefficient_values",
            "derive_alpha_K_radial_coefficient_values",
            "write_counterterm_alpha_res_radial_components",
            "convert_to_counterterm_trace_residual_inputs",
            "emit_R_h_ab_and_R_K_ab_tensors",
        ],
        "primary_blocker": "none"
        if ready
        else "derive_alpha_h_alpha_K_radial_coefficients_from_full_sigma_variation",
        "gate_passed": ready,
        "next_required": []
        if ready
        else [
            "derive_alpha_h_radial_coefficient_values_from_full_Sigma_boundary_variation",
            "derive_alpha_K_radial_coefficient_values_from_full_Sigma_boundary_variation",
            "do_not_use_minimal_basis_to_infer_traces_without_boundary_condition",
        ],
        "verdict": (
            "The downstream machinery from alpha radial components to R_h/R_K tensors "
            "is now complete. The only remaining mathematical input is the actual "
            "full Sigma boundary variation producing alpha_h_radial and alpha_K_radial."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma R_h/R_K Trace Derivation Frontier Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["verdict"],
        "",
        "## Route order",
    ]
    lines.extend(f"- `{item}`" for item in payload["route_order"])
    lines.extend(["", "## Next required"])
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
