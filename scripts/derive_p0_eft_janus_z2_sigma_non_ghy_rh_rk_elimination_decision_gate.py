from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_alpha_res_z2_anti_invariance_obligation_gate import (
    build_payload as build_alpha_anti_invariance,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_residual_value_extraction_attempt_gate import (
    build_payload as build_tetrad_value_attempt,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_trace_target_resolution import (
    build_payload as build_trace_resolution,
)
from scripts.derive_p0_eft_janus_z2_sigma_remaining_non_ghy_counterterm_channel_audit import (
    build_payload as build_remaining_non_ghy,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/non_ghy_rh_rk_elimination_decision.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_non_ghy_rh_rk_elimination_decision_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_non_ghy_rh_rk_elimination_decision_gate.json"
)


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    remaining = build_remaining_non_ghy()
    trace = build_trace_resolution()
    alpha = build_alpha_anti_invariance()
    value_attempt = build_tetrad_value_attempt()

    rh_open = bool(remaining["open_non_GHY_channels"]["metric_non_GHY_trace_R_h"])
    rk_open = bool(remaining["open_non_GHY_channels"]["extrinsic_non_GHY_trace_R_K"])
    zero_trace_allowed = bool(trace["trace_targets"]["zero_trace_payload_allowed"])
    anti_invariance_ready = bool(alpha["closure"]["alpha_res_Z2_anti_invariance_proved"])
    values_extractable = bool(
        value_attempt["R_h_ab_value_extractable"]
        and value_attempt["R_K_ab_value_extractable"]
    )
    elimination_ready = (not rh_open and not rk_open) or zero_trace_allowed or anti_invariance_ready
    value_route_ready = values_extractable
    gate_passed = elimination_ready or value_route_ready
    payload = {
        "status": "janus-z2-sigma-non-ghy-rh-rk-elimination-decision-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_residual_route_decision",
        "routes": {
            "absence_audit_route": {
                "ready": not rh_open and not rk_open,
                "open_R_h": rh_open,
                "open_R_K": rk_open,
            },
            "zero_trace_payload_route": {
                "ready": zero_trace_allowed,
                "decision": trace["decision"],
                "primary_blockers": trace["primary_blockers"],
            },
            "Z2_anti_invariance_route": {
                "ready": anti_invariance_ready,
                "primary_blocker": alpha["primary_blocker"],
                "route_status": alpha["route_status"],
            },
            "explicit_alpha_value_route": {
                "ready": value_route_ready,
                "primary_blocker": value_attempt["primary_blocker"],
                "R_h_ab_value_extractable": value_attempt["R_h_ab_value_extractable"],
                "R_K_ab_value_extractable": value_attempt["R_K_ab_value_extractable"],
            },
        },
        "decision": (
            "eliminate_or_materialize_R_h_R_K"
            if gate_passed
            else "blocked_on_component_values_or_componentwise_Z2_parity"
        ),
        "R_h_R_K_eliminated": elimination_ready,
        "R_h_R_K_materializable": value_route_ready,
        "gate_passed": gate_passed,
        "primary_blocker": "none"
        if gate_passed
        else "alpha_res_component_values_or_componentwise_parity",
        "next_required": []
        if gate_passed
        else [
            "emit_metric_tetrad_component_value_R_h_ab",
            "emit_extrinsic_tetrad_component_value_R_K_ab",
            "or_prove_tau_Z2_pullback_alpha_h_equals_minus_alpha_h",
            "and_prove_tau_Z2_pullback_alpha_K_equals_minus_alpha_K",
        ],
        "forbidden_shortcuts": [
            "do_not_emit_zero_R_h_R_K_while_non_GHY_channels_open",
            "do_not_reintroduce_linear_K_counterterm",
            "do_not_invent_S_ct_density_to_balance_R_Sigma",
        ],
        "verdict": (
            "R_h/R_K are not eliminable yet. The viable closures are narrow: "
            "either emit explicit alpha_res metric/extrinsic values, or prove "
            "componentwise Z2 anti-invariance of alpha_h and alpha_K. Bibliography "
            "and existing partition rules do not justify setting them to zero."
        ),
        "output_manifest": str(output_path),
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Non-GHY R_h/R_K Elimination Decision Gate",
        "",
        f"Decision: `{payload['decision']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["verdict"],
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(f"- `{name}`: ready=`{route['ready']}`")
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
