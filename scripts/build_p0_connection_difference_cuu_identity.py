from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_connection_difference_cuu_identity.md")
JSON_PATH = Path("outputs/reports/p0_connection_difference_cuu_identity.json")


def build_payload() -> dict:
    gamma_receiver, gamma_source, u, du = sp.symbols("Gamma_receiver Gamma_source u du")
    c_conn = sp.simplify(gamma_receiver - gamma_source)
    a_receiver = sp.simplify(du + gamma_receiver * u**2)
    a_source = sp.simplify(du + gamma_source * u**2)
    residual_plus = sp.simplify(a_receiver - a_source - c_conn * u**2)
    residual_minus = sp.simplify(a_source - a_receiver + c_conn * u**2)
    rows = [
        {
            "row": "plus_receiver_minus_source",
            "identity": "a_receiver = a_source + C(u,u)",
            "residual": str(residual_plus),
            "closed": residual_plus == 0,
        },
        {
            "row": "minus_source_receiver",
            "identity": "a_source = a_receiver - C(u,u)",
            "residual": str(residual_minus),
            "closed": residual_minus == 0,
        },
    ]
    still_required = [
        "prove source-sector geodesic equation for the transported flow",
        "derive receiver/source connection pair from the same phi/L pullback",
        "derive D L and B4vol measure terms with the same map",
        "substitute into both R_plus and R_minus residuals",
    ]
    return {
        "description": "Algebraic identity for the cross-pullback connection-force term C(u,u).",
        "status": "connection-difference-cuu-identity-closed-algebraic",
        "definition": "C = Gamma_receiver - Gamma_source",
        "rows": rows,
        "residuals_zero": all(row["closed"] for row in rows),
        "plus_sign_closed": rows[0]["closed"],
        "minus_sign_closed": rows[1]["closed"],
        "cross_pullback_algebra_closed": True,
        "source_geodesic_required": True,
        "same_phi_l_required": True,
        "dl_b4vol_still_required": True,
        "r_plus_r_minus_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "still_required": still_required,
        "verdict": (
            "The C(u,u) sign and connection-difference algebra close exactly. This removes "
            "one local ambiguity, but residual closure still requires source geodesics and the "
            "same Janus-selected phi/L, D L, and B4vol map."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Connection-Difference Cuu Identity",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Definition: `{payload['definition']}`",
        f"Residuals zero: {payload['residuals_zero']}",
        f"Plus sign closed: {payload['plus_sign_closed']}",
        f"Minus sign closed: {payload['minus_sign_closed']}",
        f"Cross pullback algebra closed: {payload['cross_pullback_algebra_closed']}",
        f"Source geodesic required: {payload['source_geodesic_required']}",
        f"Same phi/L required: {payload['same_phi_l_required']}",
        f"DL/B4vol still required: {payload['dl_b4vol_still_required']}",
        f"R plus/R minus closed: {payload['r_plus_r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rows",
        "",
        "| row | identity | residual | closed |",
        "|---|---|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(f"| {row['row']} | `{row['identity']}` | `{row['residual']}` | {row['closed']} |")
    lines.extend(["", "## Still Required", ""])
    lines.extend(f"- {item}" for item in payload["still_required"])
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
