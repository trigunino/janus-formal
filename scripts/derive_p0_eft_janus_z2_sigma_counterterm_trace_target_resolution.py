from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_cartan_ghy_junction_trace_partition_audit import (
    build_payload as build_partition,
)
from scripts.derive_p0_eft_janus_z2_sigma_mixed_hk_trace_solution_obstruction import (
    build_payload as build_mixed_hk,
)
from scripts.derive_p0_eft_janus_z2_sigma_remaining_non_ghy_counterterm_channel_audit import (
    build_payload as build_remaining,
)
from scripts.build_p0_eft_janus_z2_sigma_active_first_action_assembly_gate import (
    build_payload as build_action,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_trace_target_resolution.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_trace_target_resolution.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_trace_target_resolution.json"
)


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    partition = build_partition()
    mixed = build_mixed_hk()
    remaining = build_remaining()
    action = build_action()
    open_non_ghy = [
        name for name, is_open in remaining["open_non_GHY_channels"].items() if is_open
    ]
    linear_k_partition_closed = bool(partition["linear_K_partition_closed"])
    mixed_requires_ghy_duplicate = bool(mixed["obstruction"]["cartan_GHY_like"])
    action_assembled = bool(action["gate_passed"])
    can_emit_zero_traces = (
        linear_k_partition_closed
        and not open_non_ghy
        and action_assembled
    )
    trace_payload_allowed = can_emit_zero_traces
    payload = {
        "status": "janus-z2-sigma-counterterm-trace-target-resolution",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_derivation",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "derivation": {
            "finite_israel_trace_partitioned_into_Cartan_GHY_junction": linear_k_partition_closed,
            "linear_K_counterterm_residual_after_partition": partition["partition"][
                "linear_K_counterterm_residual_after_partition"
            ],
            "mixed_hK_trace_match_requires_linear_K_duplicate": mixed_requires_ghy_duplicate,
            "counterterm_c1_after_partition": partition["partition"][
                "counterterm_c1_after_partition"
            ],
            "remaining_non_GHY_channels": open_non_ghy,
            "active_first_action_assembled": action_assembled,
        },
        "trace_targets": {
            "R_h_trace_values_ready": False,
            "R_K_trace_values_ready": False,
            "zero_trace_payload_allowed": trace_payload_allowed,
            "counterterm_trace_residual_inputs_allowed": trace_payload_allowed,
        },
        "decision": (
            "do_not_emit_counterterm_trace_residual_inputs"
            if not trace_payload_allowed
            else "emit_zero_counterterm_trace_residual_inputs"
        ),
        "reason": (
            "The finite throat trace is already assigned to Cartan-GHY/junction. "
            "The only minimal mixed h,K match needs a forbidden linear-K duplicate. "
            "The remaining non-GHY R_h/R_K channels and active S_cross blocker are "
            "still open, so zero residual traces cannot be emitted as a proof."
        )
        if not trace_payload_allowed
        else (
            "All non-GHY channels are absent and the active first action is assembled; "
            "the residual counterterm traces can be emitted as zero."
        ),
        "primary_blockers": []
        if trace_payload_allowed
        else [
            *open_non_ghy,
            *([] if action_assembled else ["cross_action_source_accepted"]),
        ],
        "next_required": []
        if trace_payload_allowed
        else [
            "derive_or_eliminate_metric_non_GHY_trace_R_h",
            "derive_or_eliminate_extrinsic_non_GHY_trace_R_K",
            "source_accept_or_remove_S_cross_from_active_first_action",
        ],
        "forbidden_shortcuts": [
            "do_not_emit_zero_R_h_R_K_while_non_GHY_channels_open",
            "do_not_use_linear_K_counterterm_duplicate",
            "do_not_treat_S_cross_new_axiom_candidate_as_source_accepted",
        ],
        "output_manifest": str(output_path),
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Trace Target Resolution",
        "",
        f"Decision: `{payload['decision']}`",
        f"Trace payload allowed: `{payload['trace_targets']['counterterm_trace_residual_inputs_allowed']}`",
        "",
        payload["reason"],
        "",
        "## Primary Blockers",
    ]
    lines.extend(f"- `{item}`" for item in payload["primary_blockers"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
