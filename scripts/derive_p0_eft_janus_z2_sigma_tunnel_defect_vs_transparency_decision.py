from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_m30_z2_symmetric_force_cancellation import (
    build_payload as build_m30_z2_cancellation,
)
from scripts.build_p0_eft_janus_z2_sigma_tunnel_junction_condition_gate import (
    build_payload as build_junction_condition,
)
from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_smooth_atlas_gate import (
    build_payload as build_smooth_atlas,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_tunnel_defect_vs_transparency_decision.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_tunnel_defect_vs_transparency_decision.json"
)


def build_payload() -> dict:
    cancellation = build_m30_z2_cancellation()
    junction = build_junction_condition()
    atlas = build_smooth_atlas()
    decision_criteria = {
        "strict_Z2_bulk_force_cancels": cancellation["formulae"]["force_after_Z2"] == "F_Sigma = 0",
        "smooth_topological_tunnel_available": bool(
            atlas["resolved_tunnel_smooth_atlas_ready"]
        ),
        "active_metric_embedding_available": not bool(
            atlas["active_metric_embedding_not_claimed"]
        ),
        "z2_junction_condition_available": bool(
            junction["z2_tunnel_junction_condition_derived"]
        ),
        "independent_tunnel_defect_action_source_found": False,
        "localized_defect_density_derived": False,
        "defect_required_by_Bianchi_or_junction": False,
    }
    route = (
        "strict_transparency_preferred_until_defect_action_derived"
        if decision_criteria["strict_Z2_bulk_force_cancels"]
        and not decision_criteria["independent_tunnel_defect_action_source_found"]
        else "defect_action_route_open"
    )
    consequences = {
        "M30_bulk_channel_E_counterterm": "0",
        "may_set_total_E_counterterm_zero": False,
        "why_not_total_zero": (
            "other Sigma-local channels may still exist; this decision only kills "
            "the M30 bulk-induced counterterm channel"
        ),
        "active_RSigma_certificate_still_blocked": True,
        "next_non_arbitrary_route": "derive active metric embedding and junction stress, then test whether any residual defect is forced",
    }
    return {
        "status": "janus-z2-sigma-tunnel-defect-vs-transparency-decision",
        "active_core": "Z2_tunnel_Sigma",
        "decision_route": route,
        "decision_criteria": decision_criteria,
        "consequences": consequences,
        "gate_passed": route == "strict_transparency_preferred_until_defect_action_derived",
        "primary_blocker": "active_metric_embedding_available",
        "next_required": [
            "do not invent a defect density",
            "route M30 bulk-induced counterterm channel to zero under strict Z2",
            "derive active metric embedding X_± and junction stress S_ab",
            "check whether Bianchi/junction leaves a nonzero residual requiring a tunnel defect",
            "only then construct a defect action if residual is forced",
        ],
        "verdict": (
            "The non-arbitrary choice is strict Z2 transparency for the M30 bulk channel. "
            "A tunnel-defect action is allowed only if active metric embedding plus "
            "junction/Bianchi equations force a residual. Therefore M30 bulk does not "
            "close R_Sigma; the next physical input is active embedding/junction stress."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Tunnel Defect vs Transparency Decision",
        "",
        f"Decision route: `{payload['decision_route']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        payload["verdict"],
        "",
        "## Decision Criteria",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["decision_criteria"].items())
    lines.extend(["", "## Consequences"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["consequences"].items())
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
