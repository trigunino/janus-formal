from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_lorentz_residual_reduction.md")
JSON_PATH = Path("outputs/reports/bianchi_lorentz_residual_reduction.json")


def build_payload() -> dict:
    substitutions = [
        "K_plus^{mu nu}=rho_minus u_{-to+}^mu u_{-to+}^nu",
        "K_minus^{mu nu}=rho_plus u_{+to-}^mu u_{+to-}^nu",
        "u_{-to+}=L_minus_to_plus u_minus",
        "u_{+to-}=L_plus_to_minus u_plus",
    ]
    reduced_residuals = [
        {
            "sector": "positive",
            "residual": (
                "R_plus^mu = D_plus_nu T_plus^{mu nu} + B_plus "
                "[u_{-to+}^mu D_minus_nu(rho_minus u_{-to+}^nu) "
                "+ rho_minus u_{-to+}^nu D_minus_nu u_{-to+}^mu "
                "+ C^mu_{nu a} rho_minus u_{-to+}^a u_{-to+}^nu]"
            ),
            "not_closed_terms": [
                "D_plus_nu T_plus^{mu nu}",
                "D_minus_nu(rho_minus u_{-to+}^nu)",
                "u_{-to+}^nu D_minus_nu u_{-to+}^mu",
                "C^mu_{nu a} rho_minus u_{-to+}^a u_{-to+}^nu",
            ],
        },
        {
            "sector": "negative",
            "residual": (
                "R_minus^mu = D_minus_nu T_minus^{mu nu} + B_minus "
                "[u_{+to-}^mu D_plus_nu(rho_plus u_{+to-}^nu) "
                "+ rho_plus u_{+to-}^nu D_plus_nu u_{+to-}^mu "
                "- C^mu_{nu a} rho_plus u_{+to-}^a u_{+to-}^nu]"
            ),
            "not_closed_terms": [
                "D_minus_nu T_minus^{mu nu}",
                "D_plus_nu(rho_plus u_{+to-}^nu)",
                "u_{+to-}^nu D_plus_nu u_{+to-}^mu",
                "-C^mu_{nu a} rho_plus u_{+to-}^a u_{+to-}^nu",
            ],
        },
    ]
    closure_requirements = [
        "derive D L_minus_to_plus and D L_plus_to_minus from Janus source equations",
        "prove transported continuity equations for rho_minus u_{-to+} and rho_plus u_{+to-}",
        "prove transported acceleration terms cancel the connection-difference force terms",
        "keep B_plus/B_minus determinant gradients in the residual identities",
        "verify both R_plus^mu=0 and R_minus^mu=0 under the same transport maps",
    ]
    forbidden_shortcuts = [
        "sector geodesics alone do not close transported residuals",
        "do not drop C^mu_{nu a} K^{a nu}",
        "do not replace residual transport by a scalar Q_cross factor",
        "do not use the Lorentz branch for tensor claims before both residuals vanish",
    ]
    return {
        "description": "Residual reduction after substituting the Lorentz dust transport branch.",
        "status": "residual-reduction-target",
        "algebraic_substitution_closed": True,
        "residuals_reduced": True,
        "residuals_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "substitutions": substitutions,
        "reduced_residuals": reduced_residuals,
        "closure_requirements": closure_requirements,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "The Lorentz dust branch reduces Bianchi closure to explicit continuity, "
            "transported-acceleration, L-derivative and connection-force terms. It "
            "does not prove R_plus=0 or R_minus=0."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Lorentz Residual Reduction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Algebraic substitution closed: {payload['algebraic_substitution_closed']}",
        f"Residuals reduced: {payload['residuals_reduced']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Substitutions",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["substitutions"])
    lines.extend(["", "## Reduced Residuals", ""])
    for row in payload["reduced_residuals"]:
        lines.append(f"- `{row['sector']}`: `{row['residual']}`")
        lines.extend(f"  - open: `{item}`" for item in row["not_closed_terms"])
    lines.extend(["", "## Closure Requirements", ""])
    lines.extend(f"- {item}" for item in payload["closure_requirements"])
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
