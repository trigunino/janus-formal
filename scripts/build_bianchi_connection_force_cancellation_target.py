from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_connection_force_cancellation_target.md")
JSON_PATH = Path("outputs/reports/bianchi_connection_force_cancellation_target.json")


def build_payload() -> dict:
    continuity_targets = [
        "D_minus_nu(rho_minus u_{-to+}^nu)=0",
        "D_plus_nu(rho_plus u_{+to-}^nu)=0",
    ]
    force_targets = [
        "u_{-to+}^nu D_minus_nu u_{-to+}^mu + C^mu_{nu a} u_{-to+}^a u_{-to+}^nu = 0",
        "u_{+to-}^nu D_plus_nu u_{+to-}^mu - C^mu_{nu a} u_{+to-}^a u_{+to-}^nu = 0",
    ]
    sufficient_closure = [
        {
            "sector": "positive",
            "if": [
                "D_plus_nu T_plus^{mu nu}=0",
                "D_minus_nu(rho_minus u_{-to+}^nu)=0",
                "u_{-to+}^nu D_minus_nu u_{-to+}^mu + C^mu_{nu a} u_{-to+}^a u_{-to+}^nu = 0",
            ],
            "then": "R_plus^mu=0 for the Lorentz dust K_plus contribution",
        },
        {
            "sector": "negative",
            "if": [
                "D_minus_nu T_minus^{mu nu}=0",
                "D_plus_nu(rho_plus u_{+to-}^nu)=0",
                "u_{+to-}^nu D_plus_nu u_{+to-}^mu - C^mu_{nu a} u_{+to-}^a u_{+to-}^nu = 0",
            ],
            "then": "R_minus^mu=0 for the Lorentz dust K_minus contribution",
        },
    ]
    unresolved_inputs = [
        "derive the two force equations from Janus coupled field equations",
        "derive the transported continuity equations, including density measure",
        "prove the same L maps also generate Q_cross optical contractions",
        "verify determinant gradients B_plus/B_minus remain consistent with the residual identities",
    ]
    forbidden_shortcuts = [
        "do not assume D L=0 globally",
        "do not drop connection-force terms C^mu_{nu a}",
        "do not infer force cancellation from local Lorentz admissibility alone",
        "do not label this a Bianchi proof until all sufficient conditions are source-derived",
    ]
    return {
        "description": "Sufficient cancellation target for connection-force terms in Lorentz dust Bianchi transport.",
        "status": "sufficient-conditions-target",
        "sufficient_conditions_written": True,
        "conditions_source_derived": False,
        "residuals_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "continuity_targets": continuity_targets,
        "force_targets": force_targets,
        "sufficient_closure": sufficient_closure,
        "unresolved_inputs": unresolved_inputs,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "These equations are sufficient targets for cancelling the Lorentz dust "
            "K_plus/K_minus residual pieces. They are not yet derived from Janus "
            "source equations, so Bianchi closure remains open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Connection-Force Cancellation Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Sufficient conditions written: {payload['sufficient_conditions_written']}",
        f"Conditions source-derived: {payload['conditions_source_derived']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Continuity Targets",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["continuity_targets"])
    lines.extend(["", "## Force Targets", ""])
    lines.extend(f"- `{item}`" for item in payload["force_targets"])
    lines.extend(["", "## Sufficient Closure", ""])
    for row in payload["sufficient_closure"]:
        lines.append(f"- {row['sector']}:")
        lines.extend(f"  - if `{item}`" for item in row["if"])
        lines.append(f"  - then `{row['then']}`")
    lines.extend(["", "## Unresolved Inputs", ""])
    lines.extend(f"- {item}" for item in payload["unresolved_inputs"])
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
