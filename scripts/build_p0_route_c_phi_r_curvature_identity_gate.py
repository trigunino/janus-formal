from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_route_c_phi_r_curvature_identity_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_phi_r_curvature_identity_gate.json")


def build_payload() -> dict:
    identity_rows = [
        {
            "object": "relative_connection",
            "candidate": "A = omega_self - L phi^*omega_other L^{-1}",
            "source_status": "conditional",
            "closed": False,
        },
        {
            "object": "relative_curvature",
            "candidate": "Phi_R = R_self - L phi^*R_other L^{-1}",
            "source_status": "identity-if-phi-L-source-derived",
            "closed": False,
        },
        {
            "object": "transport",
            "candidate": "D_self L = A L",
            "source_status": "conditional",
            "closed": False,
        },
        {
            "object": "holonomy",
            "candidate": "Hol(A,loop) fixed by curvature identity and source path rule",
            "source_status": "path-rule-missing",
            "closed": False,
        },
    ]
    required_source_inputs = [
        "Janus source-derived phi or soldering map",
        "Janus-compatible tetrad/spin-connection gauge",
        "field-equation expression for R_self and phi^*R_other",
        "basepoint/boundary rule for integrating A",
        "same L reused by K, Q_cross, and Vlasov transport",
    ]
    forbidden_shortcuts = [
        "declare Phi_R as a target curvature by hand",
        "choose holonomy path family from lensing residuals",
        "use different L maps for K, Q_cross, and matter transport",
        "absorb missing curvature/holonomy terms into Q_det or Q_cross",
    ]
    return {
        "description": (
            "Route C gate: reduce free Phi_R to a computable relative-curvature "
            "identity, while refusing it as a closure unless phi, tetrads, path "
            "rule, and same-L transport are source-derived from Janus."
        ),
        "status": "phi-r-curvature-identity-gate-open",
        "route": "BF_connection/holonomy",
        "identity_rows": identity_rows,
        "required_source_inputs": required_source_inputs,
        "forbidden_shortcuts": forbidden_shortcuts,
        "free_phi_r_allowed": False,
        "phi_l_source_derived": False,
        "curvature_identity_available": True,
        "curvature_identity_sufficient": False,
        "path_rule_source_derived": False,
        "same_l_transport_closed": False,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is progress for zero-axiom Route C: Phi_R is no longer allowed "
            "as a free function; the only admissible candidate is the relative "
            "curvature identity. It still does not close because phi/L, tetrad "
            "gauge, path rule, and same-L transport remain source-derived False."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Phi_R Curvature Identity Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Route: {payload['route']}",
        f"Free Phi_R allowed: {payload['free_phi_r_allowed']}",
        f"Phi/L source derived: {payload['phi_l_source_derived']}",
        f"Curvature identity available: {payload['curvature_identity_available']}",
        f"Curvature identity sufficient: {payload['curvature_identity_sufficient']}",
        f"Path rule source derived: {payload['path_rule_source_derived']}",
        f"Same-L transport closed: {payload['same_l_transport_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| object | candidate | source status | closed |",
        "|---|---|---|---:|",
    ]
    for row in payload["identity_rows"]:
        lines.append(
            f"| {row['object']} | `{row['candidate']}` | "
            f"{row['source_status']} | {row['closed']} |"
        )
    lines.extend(["", "## Required Source Inputs", ""])
    lines.extend(f"- {item}" for item in payload["required_source_inputs"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
