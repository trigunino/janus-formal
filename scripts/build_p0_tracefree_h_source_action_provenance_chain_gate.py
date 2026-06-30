from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_source_action_provenance_chain_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_source_action_provenance_chain_gate.json")


def build_payload() -> dict:
    chain_steps = [
        {
            "step": "S_Janus[H,L,phi,matter]",
            "requirement": "accepted Janus action with H, L, phi, and matter dependence declared",
            "closed": False,
        },
        {
            "step": "declared variation domain",
            "requirement": "allowed H variations, gauge/boundary data, and trace-free channel are declared",
            "closed": False,
        },
        {
            "step": "deltaS/deltaH",
            "requirement": "Euler-Lagrange variation with respect to H is derived",
            "closed": False,
        },
        {
            "step": "P_STF projection",
            "requirement": "symmetric trace-free projection is applied after the H variation",
            "closed": False,
        },
        {
            "step": "same bridge source term",
            "requirement": "the projected term is identified with the same H/Q_TF bridge source",
            "closed": False,
        },
    ]
    origins = [
        {
            "origin": "published Janus field equation",
            "status": "conditional",
            "closed": False,
            "accepted": False,
            "blocker": "needs traceable derivation from S_Janus through the declared H variation domain",
        },
        {
            "origin": "relative-H action",
            "status": "conditional",
            "closed": False,
            "accepted": False,
            "blocker": "needs deltaS/deltaH, P_STF projection, same-bridge identification, and stability/gauge closure",
        },
        {
            "origin": "matter variation/Pi_TF",
            "status": "conditional",
            "closed": False,
            "accepted": False,
            "blocker": "needs matter variation to produce Pi_TF as the same bridge S_TF^Janus source",
        },
        {
            "origin": "Vlasov kinetic action",
            "status": "conditional",
            "closed": False,
            "accepted": False,
            "blocker": "needs Janus kinetic action, moment closure, and projected H source extraction",
        },
        {
            "origin": "BF/GL constraint action",
            "status": "conditional",
            "closed": False,
            "accepted": False,
            "blocker": "needs constraint multiplier variation to derive the same bridge trace-free source",
        },
    ]
    rejected_routes = [
        {
            "route": "residual_source",
            "accepted": False,
            "reason": "a residual source is not source-action provenance",
        },
        {
            "route": "determinant_trace",
            "accepted": False,
            "reason": "determinant/log-det data is trace data, not an H/Q_TF trace-free source",
        },
    ]
    return {
        "description": (
            "Bounded P0 gate for trace-free H/Q_TF source-action provenance "
            "of S_TF^Janus."
        ),
        "status": "tracefree-h-source-action-provenance-chain-gate-open",
        "accepted_s_tf_janus_requires_chain": (
            "S_Janus[H,L,phi,matter] -> declared variation domain -> "
            "deltaS/deltaH -> P_STF projection -> same bridge source term"
        ),
        "source_symbol": "S_TF^Janus",
        "bridge": "H/Q_TF",
        "chain_steps": chain_steps,
        "candidate_origins": origins,
        "rejected_routes": rejected_routes,
        "all_chain_steps_closed": False,
        "all_origins_unclosed_or_conditional": True,
        "any_origin_accepted": False,
        "source_action_provenance_closed": False,
        "same_bridge_source_term_closed": False,
        "residual_source_allowed": False,
        "determinant_trace_allowed": False,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "No S_TF^Janus provenance origin is accepted. The trace-free "
            "H/Q_TF source remains conditional until the full source-action "
            "chain closes on the same bridge."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Source-Action Provenance Chain Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source symbol: `{payload['source_symbol']}`",
        f"Bridge: `{payload['bridge']}`",
        f"Accepted chain: `{payload['accepted_s_tf_janus_requires_chain']}`",
        f"All chain steps closed: {payload['all_chain_steps_closed']}",
        f"All origins unclosed or conditional: {payload['all_origins_unclosed_or_conditional']}",
        f"Any origin accepted: {payload['any_origin_accepted']}",
        f"Source-action provenance closed: {payload['source_action_provenance_closed']}",
        f"Same bridge source term closed: {payload['same_bridge_source_term_closed']}",
        f"Residual source allowed: {payload['residual_source_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Required Chain",
        "",
        "| step | requirement | closed |",
        "|---|---|---:|",
    ]
    for row in payload["chain_steps"]:
        lines.append(f"| {row['step']} | {row['requirement']} | {row['closed']} |")
    lines.extend(
        [
            "",
            "## Candidate Provenance Origins",
            "",
            "| origin | status | closed | accepted | blocker |",
            "|---|---|---:|---:|---|",
        ]
    )
    for row in payload["candidate_origins"]:
        lines.append(
            f"| {row['origin']} | {row['status']} | {row['closed']} | "
            f"{row['accepted']} | {row['blocker']} |"
        )
    lines.extend(
        [
            "",
            "## Rejected Routes",
            "",
            "| route | accepted | reason |",
            "|---|---:|---|",
        ]
    )
    for row in payload["rejected_routes"]:
        lines.append(f"| {row['route']} | {row['accepted']} | {row['reason']} |")
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
