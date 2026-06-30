from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_dl_velocity_cancellation.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_dl_velocity_cancellation.json")


def build_payload() -> dict:
    cancellation_inputs = [
        {
            "input": "E_L",
            "role": "Stueckelberg tetrad equation for transported-frame variations",
            "cancels_terms": ["antisymmetric D_L tetrad projection"],
            "closed": False,
        },
        {
            "input": "Lorentz constraint",
            "role": "enforces L^T eta L=eta and antisymmetric Lorentz-generator D_L sector",
            "cancels_terms": ["symmetric D_L tetrad projection"],
            "closed": False,
        },
        {
            "input": "same-L K/Qcross",
            "role": "uses one transported Lorentz map in K tensors and Q_cross contractions",
            "cancels_terms": ["inconsistent K/Q_cross tetrad drift"],
            "closed": False,
        },
        {
            "input": "transported geodesic dust",
            "role": "sets u_to dot D_self u_to only after transport and connection terms are accounted",
            "cancels_terms": ["direct transported-velocity acceleration"],
            "closed": False,
        },
        {
            "input": "transported dust continuity",
            "role": "removes density-divergence product-rule terms in D_self(K_self)",
            "cancels_terms": ["rho_to D_self u_to divergence partner"],
            "closed": False,
        },
    ]
    residual_terms = [
        {
            "term": "D_L transported tetrad",
            "schematic": "rho_to u_to^alpha u_to^beta D_self L",
            "tested_by": ["E_L", "Lorentz constraint", "same-L K/Qcross"],
            "status": "conditional",
        },
        {
            "term": "D_L transported velocity",
            "schematic": "rho_to u_to^nu D_self_nu u_to^mu",
            "tested_by": ["transported geodesic dust", "transported dust continuity"],
            "status": "conditional",
        },
        {
            "term": "connection-difference residual",
            "schematic": "rho_to C_self-other^mu_{alpha beta} u_to^alpha u_to^beta",
            "tested_by": ["transported geodesic dust"],
            "status": "open",
        },
    ]
    sectors = [
        {
            "sector": "plus",
            "k_tensor": "K_plus^{mu nu}=B_minus_to_plus rho_minus_to_plus u_-to+^mu u_-to+^nu",
            "residual": "D_plus_nu K_plus^{mu nu}",
            "transport_connection": "C_plus-minus",
            "closed": False,
        },
        {
            "sector": "minus",
            "k_tensor": "K_minus^{mu nu}=B_plus_to_minus rho_plus_to_minus u_+to-^mu u_+to-^nu",
            "residual": "D_minus_nu K_minus^{mu nu}",
            "transport_connection": "C_minus-plus",
            "closed": False,
        },
    ]
    conditional_closure_conditions = [
        "E_L must exactly match the D_L tetrad variation in both residual sectors",
        "Lorentz constraint must eliminate only gauge/tetrad-generator pieces, not physical connection differences",
        "same transported L must be used in K and Q_cross with no extra fit parameter",
        "transported geodesic and continuity equations must be source-derived in the receiving connection",
        "connection-difference residual C_self-other u_to u_to must vanish or be canceled by a derived identity",
    ]
    return {
        "description": (
            "Bounded P0 artifact testing whether zero-parameter Stueckelberg dust "
            "cancels D_L transported velocity/tetrad terms in the K residuals."
        ),
        "status": "dl-velocity-tetrad-cancellation-conditional-open",
        "branch": "zero_parameter_stueckelberg_dust",
        "fit_used": False,
        "free_parameters": [],
        "same_l_k_qcross_required": True,
        "e_l_included": True,
        "lorentz_constraint_included": True,
        "transported_geodesic_included": True,
        "transported_continuity_included": True,
        "connection_difference_residual_included": True,
        "dl_tetrad_terms_cancel": "conditional",
        "dl_velocity_terms_cancel": "conditional",
        "connection_difference_residual_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "cancellation_inputs": cancellation_inputs,
        "residual_terms": residual_terms,
        "sectors": sectors,
        "conditional_closure_conditions": conditional_closure_conditions,
        "verdict": (
            "E_L, the Lorentz constraint, same-L K/Q_cross consistency, and transported "
            "geodesic/continuity equations can localize the D_L transported tetrad and "
            "velocity pieces, but closure remains conditional because the receiving-connection "
            "difference residual is not proven zero. No fit is introduced, and prediction "
            "readiness remains false."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg D_L Velocity/Tetrad Cancellation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Branch: {payload['branch']}",
        f"Fit used: {payload['fit_used']}",
        f"Free parameters: {payload['free_parameters']}",
        f"Same-L K/Qcross required: {payload['same_l_k_qcross_required']}",
        f"D_L tetrad terms cancel: {payload['dl_tetrad_terms_cancel']}",
        f"D_L velocity terms cancel: {payload['dl_velocity_terms_cancel']}",
        f"Connection-difference residual closed: {payload['connection_difference_residual_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Cancellation Inputs",
        "",
    ]
    for row in payload["cancellation_inputs"]:
        lines.append(f"- {row['input']}: {row['role']}")
        lines.append(f"  - cancels terms: {row['cancels_terms']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Residual Terms", ""])
    for row in payload["residual_terms"]:
        lines.append(f"- {row['term']}: `{row['schematic']}`")
        lines.append(f"  - tested by: {row['tested_by']}")
        lines.append(f"  - status: {row['status']}")
    lines.extend(["", "## Sectors", ""])
    for row in payload["sectors"]:
        lines.append(f"- {row['sector']}: `{row['residual']}`")
        lines.append(f"  - K tensor: `{row['k_tensor']}`")
        lines.append(f"  - transport connection: {row['transport_connection']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Conditional Closure Conditions", ""])
    lines.extend(f"- {item}" for item in payload["conditional_closure_conditions"])
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
