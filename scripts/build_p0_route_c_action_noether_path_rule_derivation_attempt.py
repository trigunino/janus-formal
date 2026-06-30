from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_indirect_path_rule_source_audit import (
    build_payload as build_indirect,
)
from scripts.build_p0_route_c_no_path_rule_underselection_theorem import (
    build_payload as build_underselection,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_action_noether_path_rule_derivation_attempt.md")
JSON_PATH = Path("outputs/reports/p0_route_c_action_noether_path_rule_derivation_attempt.json")


def build_payload() -> dict:
    indirect = build_indirect()
    underselection = build_underselection()
    rows = [
        {
            "route": "diffeomorphism_noether",
            "candidate_equation": "delta S = integral xi_mu nabla_nu T^{mu nu}",
            "derives_path_rule": False,
            "reason": "gives conservation/identity constraints, not a selected holonomy path family",
        },
        {
            "route": "worldline_geodesic_action",
            "candidate_equation": "delta integral ds_g = 0",
            "derives_path_rule": False,
            "reason": "selects sector geodesics only; it does not choose cross-sector same-L holonomy",
        },
        {
            "route": "reparametrization_noether",
            "candidate_equation": "H_gamma=0",
            "derives_path_rule": False,
            "reason": "fixes a parametrization constraint, not the path family",
        },
        {
            "route": "bf_connection_noether",
            "candidate_equation": "F_Omega=Phi_R and D L=Omega L",
            "derives_path_rule": False,
            "reason": "fixes curvature/transport equations but leaves noncommuting path order freedom",
        },
        {
            "route": "wilson_line_path_action",
            "candidate_equation": "delta_gamma Tr P exp integral_gamma Omega = 0",
            "derives_path_rule": "only as new variational principle",
            "reason": "would be an explicit path-selection action not present in Janus sources",
        },
        {
            "route": "matter_pullback_action",
            "candidate_equation": "delta_phi S_matter[pullback]=0",
            "derives_path_rule": False,
            "reason": "can constrain matter image maps, but does not select optical/holonomy path family",
        },
    ]
    return {
        "description": (
            "Attempt to derive the Route C holonomy path rule from action/Noether "
            "structures instead of choosing it as a new boundary/path axiom."
        ),
        "status": "action-noether-path-rule-derivation-attempt-obstructed",
        "depends_on": [
            "p0_route_c_indirect_path_rule_source_audit",
            "p0_route_c_no_path_rule_underselection_theorem",
        ],
        "indirect_source_found": bool(indirect["indirect_path_rule_source_found"]),
        "underselection_bounded_no_go_closed": bool(underselection["bounded_no_go_closed"]),
        "rows": rows,
        "candidate_count": len(rows),
        "accepted_zero_axiom_derivation_count": sum(row["derives_path_rule"] is True for row in rows),
        "action_noether_path_rule_derived": False,
        "noether_derives_constraints_not_selector": True,
        "wilson_line_action_is_possible_extension": True,
        "wilson_line_action_adopted": False,
        "new_axiom_if_wilson_line_adopted": True,
        "zero_axiom_path_rule_selected": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The action/Noether attempt does not derive a zero-axiom path rule. "
            "Noether identities constrain conservation and transport equations, while "
            "a Wilson-line/path action would be a new explicit extension, not a "
            "published Janus consequence."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Action/Noether Path-Rule Derivation Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Indirect source found: {payload['indirect_source_found']}",
        f"Underselection bounded no-go closed: {payload['underselection_bounded_no_go_closed']}",
        f"Candidate count: {payload['candidate_count']}",
        f"Accepted zero-axiom derivation count: {payload['accepted_zero_axiom_derivation_count']}",
        f"Action/Noether path rule derived: {payload['action_noether_path_rule_derived']}",
        f"Noether derives constraints not selector: {payload['noether_derives_constraints_not_selector']}",
        f"Wilson-line action possible extension: {payload['wilson_line_action_is_possible_extension']}",
        f"Wilson-line action adopted: {payload['wilson_line_action_adopted']}",
        f"New axiom if Wilson-line adopted: {payload['new_axiom_if_wilson_line_adopted']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| route | candidate equation | derives path rule | reason |",
        "|---|---|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['route']} | `{row['candidate_equation']}` | "
            f"{row['derives_path_rule']} | {row['reason']} |"
        )
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
