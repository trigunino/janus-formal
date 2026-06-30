from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_bianchi_mixed_transport_map_target import (
    build_payload as build_bianchi_mixed_transport,
)
from scripts.build_p0_same_l_bridge_induces_m_k_qcross_gate import (
    build_payload as build_same_l_bridge_stack,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_janus_coupled_stress_stf_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_janus_coupled_stress_stf_transport_gate.json")


def build_payload() -> dict:
    bianchi_transport = build_bianchi_mixed_transport()
    same_l_bridge_stack = build_same_l_bridge_stack()
    transport_definitions = [
        {
            "name": "bridge_map",
            "formula": "M_{o->s}^{mu}{}_{alpha}=e_s^{mu}{}_A L_{o->s}^{A}{}_B e_o^{B}{}_{alpha}",
            "meaning": "same tetrad bridge maps other-sector tensor indices into self-sector indices",
        },
        {
            "name": "transported_stress",
            "formula": "T_{o->s}^{mu nu}=M_{o->s}^{mu}{}_{alpha} M_{o->s}^{nu}{}_{beta} T_o^{alpha beta}",
            "meaning": "rank-2 symmetric tensor transport when T_o is symmetric",
        },
        {
            "name": "coupled_source_plus",
            "formula": "S_+^{mu nu}=T_+^{mu nu}+B_+ T_{-->+}^{mu nu}",
            "meaning": "M15/M30 plus-sector coupled tensor source after bridge transport",
        },
        {
            "name": "coupled_source_minus",
            "formula": "S_-^{mu nu}=B_- T_{+->-}^{mu nu}+T_-^{mu nu}",
            "meaning": "minus-sector coupled tensor source; field-equation sign is external to STF type",
        },
        {
            "name": "tracefree_projection",
            "formula": "X_TF,s^{mu nu}=P_STF^s(S_s) = S_s^{(mu nu)} - (1/4) g_s^{mu nu} g^s_{alpha beta} S_s^{alpha beta}",
            "meaning": "4D symmetric trace-free rank-2 source candidate",
        },
    ]
    algebraic_results = [
        {
            "claim": "rank2_transport",
            "result": "T_{o->s}^{mu nu} is a self-sector rank-2 tensor if M_{o->s} is a bridge map",
            "closed": True,
        },
        {
            "claim": "symmetry_preserved",
            "result": "T_o^{alpha beta}=T_o^{beta alpha} implies T_{o->s}^{mu nu}=T_{o->s}^{nu mu}",
            "closed": True,
        },
        {
            "claim": "stf_type",
            "result": "P_STF^s(S_s) is symmetric and satisfies g^s_{mu nu} X_TF,s^{mu nu}=0",
            "closed": True,
        },
        {
            "claim": "rank_count",
            "result": "in 4D, symmetric rank-2 has 10 components and STF projection leaves 9",
            "closed": True,
        },
        {
            "claim": "scalar_absorption_blocked",
            "result": "B4vol is only a scalar multiplier of T_{o->s}; its trace alone cannot be X_TF",
            "closed": True,
        },
    ]
    open_requirements = [
        "source-select the same admissible L that algebraically induces M, K, Q_cross and Vlasov",
        "prove M_{+->-} is the mirror/inverse branch of M_{-->+}",
        "fix B4vol/J/lapse measure convention without mixing Q_det/Q_cross",
        "include delta M, delta B4vol, delta P_STF and delta_mu in action variation",
        "show both R_plus=0 and R_minus=0 with the same bridge before predictions",
    ]
    return {
        "description": "Same-bridge transport derivation for the Janus coupled-stress STF X_TF candidate.",
        "status": "janus-coupled-stress-stf-transport-algebra-closed-source-open",
        "target_channel": "H_TF/Q_TF",
        "source_anchors": ["M15 Eqs. 4a-4b", "M30 Eqs. 105a-105b", "Bianchi mixed transport target"],
        "depends_on": [
            "bianchi_mixed_transport_map_target",
            "p0_same_l_bridge_induces_m_k_qcross_gate",
        ],
        "mixed_transport_physics_closed": bool(bianchi_transport["physics_closed"]),
        "same_l_bridge_stack_artifact": "p0_same_l_bridge_induces_m_k_qcross_gate",
        "same_l_bridge_stack_algebra_closed": bool(
            same_l_bridge_stack["same_l_stack_algebra_closed"]
        ),
        "same_l_bridge_stack_source_selected": bool(same_l_bridge_stack["l_source_selected"]),
        "same_l_induces_m": bool(same_l_bridge_stack["same_l_induces_m"]),
        "same_l_induces_k": bool(same_l_bridge_stack["same_l_induces_k"]),
        "same_l_induces_qcross": bool(same_l_bridge_stack["same_l_induces_qcross"]),
        "same_l_induces_vlasov_moments": bool(
            same_l_bridge_stack["same_l_induces_vlasov_moments"]
        ),
        "best_xtf_candidate": "janus_coupled_stress_stf",
        "transport_definitions": transport_definitions,
        "algebraic_results": algebraic_results,
        "algebraic_transport_closed": True,
        "stf_rank2_coherent": True,
        "rank_4d_symmetric": 10,
        "rank_4d_stf": 9,
        "scalar_absorption_allowed": False,
        "same_bridge_source_selected": False,
        "transport_acceptance_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "open_requirements": open_requirements,
        "verdict": (
            "The same-bridge tensor algebra is derived: transported coupled stress "
            "has a coherent 4D STF rank-2 projection. This is not yet a physical "
            "closure because the common bridge M/L, measure branch and variation "
            "dependencies are still source-open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Janus Coupled-Stress STF Transport Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Best X_TF candidate: `{payload['best_xtf_candidate']}`",
        f"Same-L bridge stack artifact: `{payload['same_l_bridge_stack_artifact']}`",
        f"Same-L bridge stack algebra closed: {payload['same_l_bridge_stack_algebra_closed']}",
        f"Same-L bridge stack source selected: {payload['same_l_bridge_stack_source_selected']}",
        f"Algebraic transport closed: {payload['algebraic_transport_closed']}",
        f"STF rank-2 coherent: {payload['stf_rank2_coherent']}",
        f"4D symmetric rank: {payload['rank_4d_symmetric']}",
        f"4D STF rank: {payload['rank_4d_stf']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"Same bridge source selected: {payload['same_bridge_source_selected']}",
        f"Transport acceptance closed: {payload['transport_acceptance_closed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Transport Definitions",
        "",
        "| name | formula | meaning |",
        "|---|---|---|",
    ]
    for row in payload["transport_definitions"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['meaning']} |")
    lines.extend(["", "## Algebraic Results", "", "| claim | result | closed |", "|---|---|---:|"])
    for row in payload["algebraic_results"]:
        lines.append(f"| {row['claim']} | {row['result']} | {row['closed']} |")
    lines.extend(["", "## Open Requirements", ""])
    lines.extend(f"- {item}" for item in payload["open_requirements"])
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
