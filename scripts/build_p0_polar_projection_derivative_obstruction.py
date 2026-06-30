from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_polar_projection_derivative_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_polar_projection_derivative_obstruction.json")


def build_payload() -> dict:
    derivative_identities = [
        (
            "L_Lorentz = polar_eta(L_geom) = L_geom H^{-1/2}, "
            "H = eta^{-1} L_geom^T eta L_geom"
        ),
        (
            "D_alpha L_Lorentz = (D_alpha L_geom) H^{-1/2} "
            "+ L_geom D_alpha(H^{-1/2})"
        ),
        (
            "D_alpha H = eta^{-1} (D_alpha L_geom)^T eta L_geom "
            "+ eta^{-1} L_geom^T eta (D_alpha L_geom)"
        ),
    ]
    square_root_obligations = [
        {
            "unknown": "X_alpha = D_alpha H^{1/2}",
            "obligation": "H^{1/2} X_alpha + X_alpha H^{1/2} = D_alpha H",
            "type": "Sylvester/Lyapunov-type derivative of the square root",
            "closed": False,
        },
        {
            "unknown": "Y_alpha = D_alpha H^{-1/2}",
            "obligation": (
                "D_alpha(H^{-1/2}) = -H^{-1/2} X_alpha H^{-1/2} "
                "on the selected regular branch"
            ),
            "type": "inverse-square-root derivative induced by X_alpha",
            "closed": False,
        },
    ]
    regularity_conditions = [
        "L_geom is invertible on the evaluated patch",
        "H=eta^{-1} L_geom^T eta L_geom admits a real smooth square-root branch",
        "the Sylvester operator A -> H^{1/2} A + A H^{1/2} is solvable on the selected branch",
        "no eigenvalue/branch-cut crossing or defective component occurs along D_alpha",
        "proper/orthochronous Lorentz component and time orientation are fixed",
    ]
    component_conditions = [
        "track determinant sign and time orientation for L_Lorentz",
        "do not mix disconnected Lorentz components across the patch",
        "verify eta-adjoint conventions before comparing plus/minus-sector components",
        "regularity is local; singular or discontinuous polar data invalidates the derivative artifact",
    ]
    blockers = [
        "D_alpha L_Lorentz is not just D_alpha L_geom because D_alpha(H^{-1/2}) generally does not commute away",
        "same-L K/Q_cross obligation remains open for the projected L_Lorentz",
        "zero-divergence/Bianchi residual closure still requires the projected derivative source equation",
        "polar projection cannot be treated as a fitted shortcut or calibration rule",
    ]
    rejection_rules = [
        "do not drop the L_geom D_alpha(H^{-1/2}) product-rule term",
        "do not assume H commutes with D_alpha H unless source equations prove the special case",
        "do not use polar_eta as an observationally fitted shortcut for L transport",
        "do not use one L for K transport and another L for Q_cross projection",
    ]
    return {
        "description": "Bounded P0 artifact for the derivative obstruction of L_Lorentz=polar_eta(L_geom).",
        "status": "derivative-obstruction-open",
        "definition": "L_Lorentz=polar_eta(L_geom)",
        "source_derived": False,
        "prediction_ready": False,
        "d_lorentz_equals_d_geom": False,
        "projection_derivative_closed": False,
        "square_root_obligation_closed": False,
        "same_l_for_k_and_qcross_source_derived": False,
        "fitted_shortcut_allowed": False,
        "derivative_identities": derivative_identities,
        "square_root_obligations": square_root_obligations,
        "regularity_conditions": regularity_conditions,
        "component_conditions": component_conditions,
        "blockers": blockers,
        "rejection_rules": rejection_rules,
        "verdict": (
            "The eta-polar projection changes the derivative problem: "
            "D_alpha L_Lorentz contains the noncommuting derivative of H^{-1/2}. "
            "A regular-branch Sylvester/Lyapunov square-root derivative, component "
            "control, and same-L K/Q_cross proof are still source-derived blockers."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Polar Projection Derivative Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Definition: `{payload['definition']}`",
        f"Source-derived: {payload['source_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"D L_Lorentz equals D L_geom: {payload['d_lorentz_equals_d_geom']}",
        f"Projection derivative closed: {payload['projection_derivative_closed']}",
        f"Square-root obligation closed: {payload['square_root_obligation_closed']}",
        f"Same L for K and Q_cross source-derived: {payload['same_l_for_k_and_qcross_source_derived']}",
        f"Fitted shortcut allowed: {payload['fitted_shortcut_allowed']}",
        "",
        "## Derivative Identities",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["derivative_identities"])
    lines.extend(["", "## Square-Root Obligations", ""])
    for row in payload["square_root_obligations"]:
        lines.append(f"- {row['unknown']}: `{row['obligation']}`")
        lines.append(f"  - type: {row['type']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Regularity Conditions", ""])
    lines.extend(f"- {item}" for item in payload["regularity_conditions"])
    lines.extend(["", "## Component Conditions", ""])
    lines.extend(f"- {item}" for item in payload["component_conditions"])
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
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
