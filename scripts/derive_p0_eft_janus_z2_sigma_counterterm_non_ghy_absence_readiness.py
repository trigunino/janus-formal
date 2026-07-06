from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_first_action_assembly_gate import (
    build_payload as build_action_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_remaining_non_ghy_counterterm_channel_audit import (
    build_payload as build_remaining_payload,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_non_ghy_absence_readiness.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_non_ghy_absence_readiness.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_non_ghy_absence_readiness.json")


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    action = build_action_payload()
    remaining = build_remaining_payload()
    action_ready = bool(action["gate_passed"])
    known_partition_clean = all(remaining["known_zero_after_partition"].values())
    no_open_non_ghy_channels = not any(remaining["open_non_GHY_channels"].values())
    payload = {
        "status": "janus-z2-sigma-counterterm-non-ghy-absence-readiness",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_action_support_audit",
        "known_partition_clean": known_partition_clean,
        "no_open_non_GHY_channels": no_open_non_ghy_channels,
        "active_first_action_assembled": action_ready,
        "action_blockers": action["blockers"],
        "can_prove_remaining_non_GHY_absence": (
            known_partition_clean and no_open_non_ghy_channels and action_ready
        ),
        "can_promote_E_counterterm_zero": False,
        "reason": (
            "The linear K, torsion-pullback, and radial Immirzi channels are clean, "
            "and the matter-flux residual is closed on the selected perfect-fluid "
            "tangential branch. E_counterterm=0 still requires both no open non-GHY "
            "channels and a fully assembled active first action."
        ),
        "next_required": [
            "accept_or_reject_S_cross_transport_source_without_Z4_reuse",
            "rerun_remaining_non_GHY_counterterm_channel_audit",
            "only_then_allow_conditional_E_counterterm_zero_if_no_sources_remain",
        ],
        "forbidden_shortcuts": [
            "do_not_prove_absence_from_incomplete_action",
            "do_not_drop_matter_or_cross_transport_channels",
            "do_not_promote_no_fit_before_active_first_action_assembled",
        ],
        "upstream": {
            "active_first_action": {
                "gate": action["status"],
                "passed": action["gate_passed"],
                "primary_blocker": action["primary_blocker"],
                "blockers": action["blockers"],
            },
            "remaining_non_GHY": {
                "gate": remaining["status"],
                "known_zero_after_partition": remaining["known_zero_after_partition"],
                "open_non_GHY_channels": remaining["open_non_GHY_channels"],
                "no_open_non_GHY_channels": no_open_non_ghy_channels,
            },
        },
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
        "# Janus Z2/Sigma Counterterm Non-GHY Absence Readiness",
        "",
        payload["reason"],
        "",
        f"Known partition clean: `{payload['known_partition_clean']}`",
        f"No open non-GHY channels: `{payload['no_open_non_GHY_channels']}`",
        f"Active first action assembled: `{payload['active_first_action_assembled']}`",
        f"Can prove non-GHY absence: `{payload['can_prove_remaining_non_GHY_absence']}`",
        "",
        "## Action Blockers",
    ]
    lines.extend(f"- `{item}`" for item in payload["action_blockers"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
