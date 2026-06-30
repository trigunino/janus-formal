from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_bf_connection_constraint_route import build_payload as build_bf
from scripts.build_p0_holonomy_loop_consistency_criteria import build_payload as build_holonomy
from scripts.build_p0_route_c_phi_r_curvature_identity_gate import build_payload as build_phi_r_identity
from scripts.build_p0_route_c_phi_r_relative_curvature_selector_probe import (
    build_payload as build_phi_r_probe,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_bf_holonomy_priority_attack.md")
JSON_PATH = Path("outputs/reports/p0_route_c_bf_holonomy_priority_attack.json")


def build_payload() -> dict:
    bf = build_bf()
    holonomy = build_holonomy()
    phi_r_identity = build_phi_r_identity()
    phi_r_probe = build_phi_r_probe()
    attack_rows = [
        {
            "target": "source_curvature",
            "equation": "F_Omega=Phi_R[source Janus]",
            "test": "is Phi_R computable from Janus metric/source rows without free functions?",
            "closed": False,
        },
        {
            "target": "transport",
            "equation": "D_alpha L=Omega_alpha L",
            "test": "does one L generate K, Q_cross and Vlasov transport?",
            "closed": False,
        },
        {
            "target": "holonomy",
            "equation": "Hol_loop(Omega)=P exp int_loop Omega",
            "test": "are loop/path choices source-derived and mirror-invertible?",
            "closed": False,
        },
        {
            "target": "same_l_residual",
            "equation": "nabla K[L]=0 and Q_cross[L] uses same L",
            "test": "do R_plus/R_minus close without scalar absorption?",
            "closed": False,
        },
    ]
    decision = [
        {
            "case": "Phi_R source-derived and holonomy fixed",
            "result": "continue route C as strongest no-axiom candidate",
        },
        {
            "case": "Phi_R free or path rule free",
            "result": "route C becomes new-axiom-risk and cannot close prediction",
        },
        {
            "case": "same-L fails K/Q_cross/Vlasov",
            "result": "reject BF/holonomy branch for Janus transport",
        },
    ]
    return {
        "description": "Priority attack for Route C: BF/connection and holonomy no-axiom selector.",
        "status": "bf-holonomy-priority-attack-open",
        "depends_on": ["p0_bf_connection_constraint_route", "p0_holonomy_loop_consistency_criteria"],
        "attack_rows": attack_rows,
        "decision": decision,
        "bf_route_status": bf["status"],
        "holonomy_status": holonomy["status"],
        "phi_r_identity_status": phi_r_identity["status"],
        "phi_r_selector_probe_status": phi_r_probe["status"],
        "bf_same_l_for_k_qcross": bool(bf["same_l_for_k_and_qcross"]),
        "holonomy_source_derived": bool(holonomy["source_derived"]),
        "phi_r_free_insert_allowed": bool(phi_r_identity["free_phi_r_allowed"]),
        "curvature_identity_available": bool(phi_r_identity["curvature_identity_available"]),
        "weakfield_phi_r_candidate_available": phi_r_probe["phi_r_source_candidate"] == "weakfield_relative_curvature_rows",
        "phi_r_source_derived": False,
        "path_rule_source_derived": False,
        "same_l_transport_proved": False,
        "l_uniquely_selected": bool(phi_r_probe["l_uniquely_selected"]),
        "strongest_no_axiom_candidate": True,
        "new_axiom_risk": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "BF/holonomy is the strongest geometric no-axiom route, but it still hinges "
            "on Phi_R and path/holonomy rules being source-derived. Until then it is a "
            "priority attack, not a closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C BF/Holonomy Priority Attack",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"BF route status: {payload['bf_route_status']}",
        f"Holonomy status: {payload['holonomy_status']}",
        f"Phi_R identity status: {payload['phi_r_identity_status']}",
        f"Phi_R selector probe status: {payload['phi_r_selector_probe_status']}",
        f"BF same L for K/Q_cross: {payload['bf_same_l_for_k_qcross']}",
        f"Holonomy source derived: {payload['holonomy_source_derived']}",
        f"Phi_R free insert allowed: {payload['phi_r_free_insert_allowed']}",
        f"Curvature identity available: {payload['curvature_identity_available']}",
        f"Weakfield Phi_R candidate available: {payload['weakfield_phi_r_candidate_available']}",
        f"Phi_R source derived: {payload['phi_r_source_derived']}",
        f"Path rule source derived: {payload['path_rule_source_derived']}",
        f"Same-L transport proved: {payload['same_l_transport_proved']}",
        f"L uniquely selected: {payload['l_uniquely_selected']}",
        f"Strongest no-axiom candidate: {payload['strongest_no_axiom_candidate']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Attack Rows",
        "",
        "| target | equation | test | closed |",
        "|---|---|---|---:|",
    ]
    for row in payload["attack_rows"]:
        lines.append(f"| {row['target']} | `{row['equation']}` | {row['test']} | {row['closed']} |")
    lines.extend(["", "## Decision", "", "| case | result |", "|---|---|"])
    for row in payload["decision"]:
        lines.append(f"| {row['case']} | {row['result']} |")
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
