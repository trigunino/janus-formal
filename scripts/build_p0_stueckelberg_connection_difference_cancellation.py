from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_connection_difference_cancellation.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_connection_difference_cancellation.json")


def build_payload() -> dict:
    connection_terms = [
        {
            "sector": "plus",
            "connection": "C_plus-minus",
            "term": "rho_minus_to_plus C_plus-minus^mu_{alpha beta} u_-to+^alpha u_-to+^beta",
            "receiver_geodesic_condition": "u_-to+^nu D_plus_nu u_-to+^mu=0",
            "source_geodesic_condition": "u_minus^b D_minus_b u_minus^a=0",
            "transport_condition": "phi_minus_to_plus and L_minus_to_plus transport source geodesics into plus geodesics",
            "vanishes_if": "D_self u_to=0 after phi/L transport",
            "closed": "conditional",
        },
        {
            "sector": "minus",
            "connection": "C_minus-plus",
            "term": "rho_plus_to_minus C_minus-plus^a_{mu nu} u_+to-^mu u_+to-^nu",
            "receiver_geodesic_condition": "u_+to-^b D_minus_b u_+to-^a=0",
            "source_geodesic_condition": "u_plus^nu D_plus_nu u_plus^mu=0",
            "transport_condition": "phi_plus_to_minus and L_plus_to_minus transport source geodesics into minus geodesics",
            "vanishes_if": "D_self u_to=0 after phi/L transport",
            "closed": "conditional",
        },
    ]
    required_identities = [
        {
            "name": "receiver_connection_transported_geodesic",
            "equation": "D_self u_to = 0",
            "role": "absorbs C_plus-minus/C_minus-plus into the transported receiver acceleration",
            "source": "transported source geodesic equation",
            "proven_here": False,
        },
        {
            "name": "E_phi_transport_identity",
            "equation": "E_phi maps phi-variation terms to the transported geodesic condition",
            "role": "ties diffeomorphism variation to geodesic transport instead of fitting a force",
            "source": "Stueckelberg phi equation",
            "proven_here": False,
        },
        {
            "name": "E_L_transport_identity",
            "equation": "E_L maps tetrad/L variation terms to the transported frame geodesic condition",
            "role": "ties Lorentz-frame variation to receiver geodesic transport",
            "source": "Stueckelberg L equation",
            "proven_here": False,
        },
        {
            "name": "same_L_for_K_and_Qcross",
            "equation": "L used in K_plus/K_minus is the same L used in Q_cross",
            "role": "forbids independent tuning of connection cancellation and optical coupling",
            "source": "same-L K/Qcross gate",
            "proven_here": False,
        },
    ]
    cancellation_tests = [
        {
            "target": "C_plus-minus force bracket",
            "test": "substitute D_plus u_-to+=0 into D_plus_nu K_plus^{mu nu}",
            "result": "vanishes_conditionally",
            "fit_used": False,
        },
        {
            "target": "C_minus-plus force bracket",
            "test": "substitute D_minus u_+to-=0 into D_minus_nu K_minus^{a b}",
            "result": "vanishes_conditionally",
            "fit_used": False,
        },
    ]
    closure_decision = {
        "connection_difference_terms_vanish": "conditional",
        "closure": False,
        "conditional_closure_possible": True,
        "open_reason": (
            "The C_plus-minus/C_minus-plus force brackets vanish only if phi/L transport "
            "source geodesics into receiver-connection geodesics and the same L also "
            "defines K_plus/K_minus and Q_cross. That identity is related to E_phi/E_L "
            "but is not proven here."
        ),
    }
    return {
        "description": (
            "Bounded P0 artifact testing whether connection-difference force terms cancel "
            "in zero-parameter Stueckelberg dust when phi/L transport source geodesics "
            "into receiver-connection geodesics."
        ),
        "status": "connection-difference-cancellation-conditional-open",
        "branch": "zero_parameter_stueckelberg_dust",
        "fit_used": False,
        "free_parameters": [],
        "same_l_k_qcross_required": True,
        "receiver_connection_geodesic_required": True,
        "e_phi_related": True,
        "e_l_related": True,
        "connection_difference_terms_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "connection_terms": connection_terms,
        "required_identities": required_identities,
        "cancellation_tests": cancellation_tests,
        "closure_decision": closure_decision,
        "verdict": (
            "The connection-difference terms can vanish conditionally through the receiver "
            "geodesic condition D_self u_to=0. Closure remains open because the required "
            "phi/L transport identity and same-L K/Qcross compatibility are obligations, "
            "not derived no-fit closure results."
        ),
    }


def render_markdown(payload: dict) -> str:
    decision = payload["closure_decision"]
    lines = [
        "# P0 Stueckelberg Connection-Difference Cancellation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Branch: {payload['branch']}",
        f"Fit used: {payload['fit_used']}",
        f"Free parameters: {payload['free_parameters']}",
        f"Same-L K/Qcross required: {payload['same_l_k_qcross_required']}",
        f"Receiver-connection geodesic required: {payload['receiver_connection_geodesic_required']}",
        f"E_phi related: {payload['e_phi_related']}",
        f"E_L related: {payload['e_l_related']}",
        f"Connection-difference terms closed: {payload['connection_difference_terms_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Connection Terms",
        "",
    ]
    for row in payload["connection_terms"]:
        lines.append(f"- {row['sector']}: `{row['term']}`")
        lines.append(f"  - connection: {row['connection']}")
        lines.append(f"  - receiver geodesic condition: `{row['receiver_geodesic_condition']}`")
        lines.append(f"  - source geodesic condition: `{row['source_geodesic_condition']}`")
        lines.append(f"  - transport condition: {row['transport_condition']}")
        lines.append(f"  - vanishes if: {row['vanishes_if']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Required Identities", ""])
    for row in payload["required_identities"]:
        lines.append(f"- {row['name']}: `{row['equation']}`")
        lines.append(f"  - role: {row['role']}")
        lines.append(f"  - source: {row['source']}")
        lines.append(f"  - proven here: {row['proven_here']}")
    lines.extend(["", "## Cancellation Tests", ""])
    for row in payload["cancellation_tests"]:
        lines.append(f"- {row['target']}: {row['result']}")
        lines.append(f"  - test: {row['test']}")
        lines.append(f"  - fit used: {row['fit_used']}")
    lines.extend(
        [
            "",
            "## Closure Decision",
            "",
            f"Connection-difference terms vanish: {decision['connection_difference_terms_vanish']}",
            f"Closure: {decision['closure']}",
            f"Conditional closure possible: {decision['conditional_closure_possible']}",
            f"Open reason: {decision['open_reason']}",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
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
