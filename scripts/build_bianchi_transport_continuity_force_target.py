from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_transport_continuity_force_target.md")
JSON_PATH = Path("outputs/reports/bianchi_transport_continuity_force_target.json")


def build_payload() -> dict:
    transported_continuity = [
        {
            "sector": "negative_to_positive",
            "equation": "D_minus_nu(rho_minus u_{-to+}^nu)=0",
            "needed_for": "R_plus^mu Lorentz dust K_plus continuity bracket",
        },
        {
            "sector": "positive_to_negative",
            "equation": "D_plus_nu(rho_plus u_{+to-}^nu)=0",
            "needed_for": "R_minus^mu Lorentz dust K_minus continuity bracket",
        },
    ]
    transported_force = [
        {
            "sector": "negative_to_positive",
            "equation": "u_{-to+}^nu D_minus_nu u_{-to+}^mu + C^mu_{nu a} u_{-to+}^a u_{-to+}^nu=0",
            "receiver_form": "u_{-to+}^nu D_plus_nu u_{-to+}^mu=0",
            "needed_for": "R_plus^mu Lorentz dust K_plus force bracket",
        },
        {
            "sector": "positive_to_negative",
            "equation": "u_{+to-}^nu D_plus_nu u_{+to-}^mu - C^mu_{nu a} u_{+to-}^a u_{+to-}^nu=0",
            "receiver_form": "u_{+to-}^nu D_minus_nu u_{+to-}^mu=0",
            "needed_for": "R_minus^mu Lorentz dust K_minus force bracket",
        },
    ]
    d_l_terms = [
        "D u_{-to+}=D(L_minus_to_plus u_minus)=(D L_minus_to_plus)u_minus+L_minus_to_plus D u_minus",
        "D u_{+to-}=D(L_plus_to_minus u_plus)=(D L_plus_to_minus)u_plus+L_plus_to_minus D u_plus",
    ]
    mirror_requirements = [
        "the same source-derived construction must define L_minus_to_plus and L_plus_to_minus",
        "the plus residual must close with K_plus and the negative residual with K_minus",
        "the C-term sign must flip between receiver connections",
        "normalization, time orientation, and Q_cross contractions must use the same L maps",
    ]
    insufficiency = [
        "same-sector dust geodesics remove only L D u terms, not (D L)u terms",
        "same-sector continuity does not imply transported continuity without the density measure and volume convention",
        "local Lorentz admissibility does not imply receiver-connection geodesic motion",
        "scalar Q_cross or Q_det factors cannot absorb vector/tensor divergence terms",
    ]
    proof_obligations = [
        "derive transported continuity from Janus source equations",
        "derive transported force equations including C from Janus source equations",
        "derive or cancel D L terms in both residuals",
        "verify R_plus^mu=0 and R_minus^mu=0 under the same transport maps",
        "extend only after dust closure to pressure and anisotropic stress",
    ]
    return {
        "description": "P0 target tying transported continuity and connection-force equations to R_plus/R_minus closure.",
        "status": "p0-transport-continuity-force-target",
        "transported_continuity_written": True,
        "transported_force_written": True,
        "d_l_terms_exposed": True,
        "mirror_equations_required": True,
        "dust_geodesics_alone_sufficient": False,
        "source_derived": False,
        "residuals_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "transported_continuity": transported_continuity,
        "transported_force": transported_force,
        "d_l_terms": d_l_terms,
        "mirror_requirements": mirror_requirements,
        "insufficiency": insufficiency,
        "proof_obligations": proof_obligations,
        "verdict": (
            "Closing Lorentz dust Bianchi residuals requires transported continuity, "
            "transported force equations with C, and control of D L terms in both "
            "directions. Dust geodesics alone are insufficient; predictions remain gated."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Transport Continuity Force Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Transported continuity written: {payload['transported_continuity_written']}",
        f"Transported force written: {payload['transported_force_written']}",
        f"D L terms exposed: {payload['d_l_terms_exposed']}",
        f"Mirror equations required: {payload['mirror_equations_required']}",
        f"Dust geodesics alone sufficient: {payload['dust_geodesics_alone_sufficient']}",
        f"Source-derived: {payload['source_derived']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Transported Continuity",
        "",
    ]
    for row in payload["transported_continuity"]:
        lines.append(f"- {row['sector']}: `{row['equation']}` -> {row['needed_for']}")
    lines.extend(["", "## Transported Force", ""])
    for row in payload["transported_force"]:
        lines.append(
            f"- {row['sector']}: `{row['equation']}`; receiver form `{row['receiver_form']}` -> {row['needed_for']}"
        )
    lines.extend(["", "## D L Terms", ""])
    lines.extend(f"- `{item}`" for item in payload["d_l_terms"])
    lines.extend(["", "## Mirror Requirements", ""])
    lines.extend(f"- {item}" for item in payload["mirror_requirements"])
    lines.extend(["", "## Insufficiency", ""])
    lines.extend(f"- {item}" for item in payload["insufficiency"])
    lines.extend(["", "## Proof Obligations", ""])
    lines.extend(f"- {item}" for item in payload["proof_obligations"])
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
