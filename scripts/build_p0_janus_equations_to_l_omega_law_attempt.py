from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_equations_to_l_omega_law_attempt.md")
JSON_PATH = Path("outputs/reports/p0_janus_equations_to_l_omega_law_attempt.json")


def build_payload() -> dict:
    janus_ingredients = [
        {
            "ingredient": "coupled_metrics",
            "source": "M15/formal/latex/janus_core_equations.tex",
            "encoded_as": "g_plus for positive geodesics; g_minus for negative geodesics",
        },
        {
            "ingredient": "coupled_field_equations",
            "source": "M15 Eqs. 4a-4b",
            "encoded_as": (
                "G_plus=chi(T_plus+B_plus T_minus); "
                "G_minus=-chi(B_minus T_plus+T_minus)"
            ),
        },
        {
            "ingredient": "determinant_factors",
            "source": "M15 determinant roots",
            "encoded_as": "B_plus=sqrt(-g_minus/-g_plus), B_minus=sqrt(-g_plus/-g_minus)",
        },
        {
            "ingredient": "bianchi_constraints",
            "source": "Bianchi: nabla_plus G_plus=0 and nabla_minus G_minus=0",
            "encoded_as": (
                "D_plus(T_plus+B_plus K_plus)=0; "
                "D_minus(B_minus K_minus+T_minus)=0"
            ),
        },
        {
            "ingredient": "cross_stress_tensors",
            "source": "P0 transport residual convention",
            "encoded_as": "K_plus and K_minus are transported stress tensors built with one L",
        },
    ]
    candidate_laws = [
        {
            "law": "dynamic_du_l",
            "formula": "Omega_alpha=(D_alpha L)L^{-1}; D_u L=Omega_u L",
            "selected_by_janus_equations": False,
            "constraint": "Bianchi exposes D L terms in K residuals but does not fix them uniquely",
        },
        {
            "law": "omega_u_u_zero",
            "formula": "Omega_u u=0",
            "selected_by_janus_equations": False,
            "constraint": (
                "rank-one dust cancellation makes this a sufficient algebraic target, "
                "not a source-derived law"
            ),
        },
    ]
    constraint_reduction = [
        {
            "step": "insert_coupled_rhs",
            "result": "Bianchi turns the coupled field equations into two RHS divergence constraints",
            "imposes_on_l_omega": "only through K_plus/K_minus once cross stress is defined",
        },
        {
            "step": "define_cross_stress_with_l",
            "result": "K_plus=rho_minus (L_minus_to_plus u_minus)^2 and mirror K_minus",
            "imposes_on_l_omega": "same L must carry both stress transport and its D L residual",
        },
        {
            "step": "differentiate_k",
            "result": "D K contains continuity, receiver-force, determinant, and D L/Omega terms",
            "imposes_on_l_omega": "residual can test a proposed Omega but does not derive it alone",
        },
        {
            "step": "dust_rank_one_check",
            "result": "Omega_u u=0 cancels the rank-one Omega residual for dust",
            "imposes_on_l_omega": "necessary/sufficient in this restricted row, not full Janus selection",
        },
        {
            "step": "qcross_lock",
            "result": "Q_cross must use the same transported tetrads/covectors as K",
            "imposes_on_l_omega": "forbids separate optical L, fitted Q_cross, or scalar absorption",
        },
    ]
    selection_status = {
        "du_l_selected": False,
        "omega_u_u_zero_selected": False,
        "same_l_for_k_qcross_required": True,
        "same_l_for_k_qcross_derived": False,
        "fitting_allowed": False,
        "scalar_absorption_allowed": False,
        "source_equations_fully_inserted": False,
        "determinant_terms_closed": False,
        "k_residual_closed": False,
        "qcross_compatibility_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
    }
    blockers = [
        "The M15 coupled equations provide determinant-weighted sources, not a unique L evolution equation.",
        "Bianchi closure constrains the divergence of the chosen K tensors but does not by itself select D_u L.",
        "Omega_u u=0 is an algebraic dust-cancellation condition until derived from the Janus source/action layer.",
        "The same L must be proved for K and Q_cross before any optical prediction is admissible.",
        "No fit, density rescaling, Q_det/Q_cross scalar absorption, or posthoc Omega choice is allowed.",
    ]
    return {
        "description": (
            "Bounded P0 attempt from Janus coupled field/source equations to a dynamic "
            "L/Omega law."
        ),
        "status": "janus-equations-to-l-omega-law-attempt-open",
        "janus_ingredients": janus_ingredients,
        "candidate_laws": candidate_laws,
        "constraint_reduction": constraint_reduction,
        "selection_status": selection_status,
        "blockers": blockers,
        **selection_status,
        "verdict": (
            "The coupled Janus equations and Bianchi identities constrain any proposed "
            "L/Omega through determinant-weighted K residuals and the shared Q_cross "
            "optical map. They do not yet select D_u L or Omega_u u=0 from source "
            "equations. Omega_u u=0 remains an algebraic dust target, and prediction_ready "
            "stays false until the same L closes K and Q_cross without fitting or scalar "
            "absorption."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Equations To L/Omega Law Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"D_u L selected: {payload['du_l_selected']}",
        f"Omega_u u=0 selected: {payload['omega_u_u_zero_selected']}",
        f"Same L for K/Q_cross required: {payload['same_l_for_k_qcross_required']}",
        f"Same L for K/Q_cross derived: {payload['same_l_for_k_qcross_derived']}",
        f"Fitting allowed: {payload['fitting_allowed']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Janus Ingredients",
        "",
        "| ingredient | source | encoded as |",
        "|---|---|---|",
    ]
    for row in payload["janus_ingredients"]:
        lines.append(f"| {row['ingredient']} | {row['source']} | `{row['encoded_as']}` |")
    lines.extend(["", "## Candidate Laws", "", "| law | formula | selected | constraint |", "|---|---|---|---|"])
    for row in payload["candidate_laws"]:
        lines.append(
            f"| {row['law']} | `{row['formula']}` | "
            f"{row['selected_by_janus_equations']} | {row['constraint']} |"
        )
    lines.extend(["", "## Constraint Reduction", "", "| step | result | imposes on L/Omega |", "|---|---|---|"])
    for row in payload["constraint_reduction"]:
        lines.append(
            f"| {row['step']} | {row['result']} | {row['imposes_on_l_omega']} |"
        )
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
