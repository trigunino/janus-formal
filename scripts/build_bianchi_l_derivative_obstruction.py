from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_l_derivative_obstruction.md")
JSON_PATH = Path("outputs/reports/bianchi_l_derivative_obstruction.json")


def build_payload() -> dict:
    product_rules = [
        "D_minus_nu u_{-to+}^mu = (D_minus_nu L_minus_to_plus^mu_a) u_minus^a + L_minus_to_plus^mu_a D_minus_nu u_minus^a",
        "u_{-to+}^nu D_minus_nu u_{-to+}^mu = u_{-to+}^nu (D_minus_nu L_minus_to_plus^mu_a) u_minus^a + u_{-to+}^nu L_minus_to_plus^mu_a D_minus_nu u_minus^a",
        "D_plus_nu u_{+to-}^mu = (D_plus_nu L_plus_to_minus^mu_a) u_plus^a + L_plus_to_minus^mu_a D_plus_nu u_plus^a",
        "u_{+to-}^nu D_plus_nu u_{+to-}^mu = u_{+to-}^nu (D_plus_nu L_plus_to_minus^mu_a) u_plus^a + u_{+to-}^nu L_plus_to_minus^mu_a D_plus_nu u_plus^a",
    ]
    geodesic_reductions = [
        {
            "assumption": "u_minus geodesic in its own sector",
            "closed_piece": "L_minus_to_plus^mu_a D_minus_u u_minus^a = 0",
            "open_piece": "u_{-to+}^nu (D_minus_nu L_minus_to_plus^mu_a) u_minus^a",
        },
        {
            "assumption": "u_plus geodesic in its own sector",
            "closed_piece": "L_plus_to_minus^mu_a D_plus_u u_plus^a = 0",
            "open_piece": "u_{+to-}^nu (D_plus_nu L_plus_to_minus^mu_a) u_plus^a",
        },
    ]
    closure_options = [
        {
            "name": "parallel_cross_transport",
            "condition": "u_{-to+}^nu D_minus_nu L_minus_to_plus = 0 and u_{+to-}^nu D_plus_nu L_plus_to_minus = 0",
            "status": "sufficient target, not derived",
        },
        {
            "name": "connection_force_cancellation",
            "condition": "rho u D L terms cancel C^mu_{nu a} K^{a nu} terms in both residuals",
            "status": "allowed target only if derived from coupled field equations",
        },
        {
            "name": "constant_local_boost",
            "condition": "D L=0 in a local patch",
            "status": "diagnostic local limit; not a global cosmological proof",
        },
    ]
    return {
        "description": "Why same-sector geodesics do not by themselves close transported Bianchi residuals.",
        "status": "obstruction-target",
        "geodesic_terms_reduced": True,
        "l_derivative_terms_open": True,
        "residuals_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "product_rules": product_rules,
        "geodesic_reductions": geodesic_reductions,
        "closure_options": closure_options,
        "verdict": (
            "Same-sector geodesics remove only the D_u u pieces. The D L pieces "
            "remain and must be derived, set parallel by a source equation, or "
            "cancelled against connection-difference forces in both residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi L-derivative Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Geodesic terms reduced: {payload['geodesic_terms_reduced']}",
        f"L-derivative terms open: {payload['l_derivative_terms_open']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Product Rules",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["product_rules"])
    lines.extend(
        [
            "",
            "## Geodesic Reductions",
            "",
            "| assumption | closed piece | open piece |",
            "|---|---|---|",
        ]
    )
    for row in payload["geodesic_reductions"]:
        lines.append(
            f"| {row['assumption']} | `{row['closed_piece']}` | `{row['open_piece']}` |"
        )
    lines.extend(
        [
            "",
            "## Closure Options",
            "",
            "| name | condition | status |",
            "|---|---|---|",
        ]
    )
    for row in payload["closure_options"]:
        lines.append(f"| {row['name']} | `{row['condition']}` | {row['status']} |")
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
