from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_tracefree_h_projector_variation_dependency_gate import (
    build_payload as build_projector_variation_dependency,
)
from scripts.build_p0_tracefree_h_frechet_log_adjoint_gate import (
    build_payload as build_frechet_log_adjoint,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_qtf_to_h_chain_rule_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_qtf_to_h_chain_rule_gate.json")


def build_payload() -> dict:
    projector_dependency = build_projector_variation_dependency()
    frechet_adjoint = build_frechet_log_adjoint()
    chain_steps = [
        {
            "step": "regular_log_branch",
            "formula": "Q = 1/2 Log(H)",
            "condition": "regular polar/log branch for the same H",
            "accepted": False,
        },
        {
            "step": "frechet_variation",
            "formula": "delta Q = 1/2 FrechetLog_H[delta H]",
            "condition": "full matrix-log Frechet derivative, not scalar log",
            "accepted": False,
        },
        {
            "step": "stf_projection",
            "formula": "delta Q_TF = P_STF(1/2 FrechetLog_H[delta H]) + projector dependency terms",
            "condition": "include projector/metric/congruence variation when they depend on H",
            "accepted": False,
        },
        {
            "step": "adjoint_pullback",
            "formula": "delta S/delta H = 1/2 FrechetLog_H^* P_STF(delta S/delta Q_TF) + dependency terms",
            "condition": "valid only as a chain rule for a source-derived action",
            "accepted": False,
        },
        {
            "step": "commuting_shortcut",
            "formula": "delta Q = 1/2 H^{-1} delta H",
            "condition": "allowed only if [H, delta H]=0 is proved on the selected branch",
            "accepted": False,
        },
    ]
    requirements = [
        "regular log/polar branch for H",
        "p0_tracefree_h_projector_variation_dependency_gate must close or stay explicit",
        "p0_tracefree_h_frechet_log_adjoint_gate must fix the adjoint branch",
        "same H, L and Omega used by Q_TF, K and Q_cross",
        "mirror inverse branch H_minus=H^{-1} and Q_minus=-Q",
        "curl integrability for D_alpha H before integrating to H",
        "boundary and gauge conditions for integration by parts",
        "Janus source/action provenance before using the result as S_TF",
    ]
    forbidden_routes = [
        "replace FrechetLog_H by a scalar trace or log det(H)",
        "use H^{-1} delta H without a proved commuting branch",
        "absorb residual targets into Q_TF or H_TF",
        "ignore projector dependency terms",
        "treat this chain rule as Janus source provenance",
    ]
    return {
        "description": "Bounded P0 gate for transporting Q_TF variations back to H variations.",
        "status": "tracefree-h-qtf-to-h-chain-rule-gate-open",
        "target_channel": "H_TF/Q_TF",
        "chain_rule_formal": True,
        "source_provenance_closed": False,
        "projector_variation_dependency_artifact": "p0_tracefree_h_projector_variation_dependency_gate",
        "projector_variation_dependency_ready": bool(projector_dependency["projector_dependency_closed"]),
        "frechet_log_adjoint_artifact": "p0_tracefree_h_frechet_log_adjoint_gate",
        "frechet_log_adjoint_ready": bool(frechet_adjoint["source_provenance_closed"]),
        "qtf_to_h_variation_ready": False,
        "accepted_as_closure": False,
        "accepted_branches": [],
        "commuting_shortcut_conditional": True,
        "commuting_shortcut_unconditional_allowed": False,
        "projector_dependency_terms_required": True,
        "same_bridge_required": True,
        "chain_steps": chain_steps,
        "requirements": requirements,
        "forbidden_routes": forbidden_routes,
        "residual_target_allowed": False,
        "determinant_trace_allowed": False,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The Q_TF-to-H chain rule is formal progress only. It converts an "
            "accepted Q_TF action variation into an H variation, but it does not "
            "supply Janus source provenance, and the scalar/commuting shortcut "
            "is forbidden unless that branch is proved."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Q_TF To H Chain Rule Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Chain rule formal: {payload['chain_rule_formal']}",
        f"Source provenance closed: {payload['source_provenance_closed']}",
        f"Projector variation dependency artifact: {payload['projector_variation_dependency_artifact']}",
        f"Projector variation dependency ready: {payload['projector_variation_dependency_ready']}",
        f"FrechetLog adjoint artifact: {payload['frechet_log_adjoint_artifact']}",
        f"FrechetLog adjoint ready: {payload['frechet_log_adjoint_ready']}",
        f"Q_TF to H variation ready: {payload['qtf_to_h_variation_ready']}",
        f"Accepted as closure: {payload['accepted_as_closure']}",
        f"Commuting shortcut unconditional allowed: {payload['commuting_shortcut_unconditional_allowed']}",
        f"Projector dependency terms required: {payload['projector_dependency_terms_required']}",
        f"Same bridge required: {payload['same_bridge_required']}",
        f"Residual target allowed: {payload['residual_target_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Chain Steps",
        "",
        "| step | formula | condition | accepted |",
        "|---|---|---|---:|",
    ]
    for row in payload["chain_steps"]:
        lines.append(
            f"| {row['step']} | `{row['formula']}` | {row['condition']} | {row['accepted']} |"
        )
    lines.extend(["", "## Requirements", ""])
    lines.extend(f"- {item}" for item in payload["requirements"])
    lines.extend(["", "## Forbidden Routes", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_routes"])
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
