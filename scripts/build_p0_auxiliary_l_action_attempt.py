from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_auxiliary_l_action_attempt.md")
JSON_PATH = Path("outputs/reports/p0_auxiliary_l_action_attempt.json")


def build_payload() -> dict:
    ansatz_terms = [
        {
            "term": "S_plus[g_plus,psi_plus] + S_minus[g_minus,psi_minus]",
            "role": "keep the two sector geodesic families and same-sector stress tensors",
            "source_status": "anchored by Janus bimetric setup",
        },
        {
            "term": "S_couple[g_plus,g_minus,L,psi_plus,psi_minus]",
            "role": "single source for K_plus, K_minus, Q_cross, and F=D L",
            "source_status": "not supplied by current sources",
        },
        {
            "term": "lambda(L^T eta L - eta)",
            "role": "constrain L to Lorentz/tetrad-admissible branch",
            "source_status": "mathematically admissible auxiliary constraint, not source-derived",
        },
    ]
    variational_tests = [
        {
            "variation": "delta S / delta g_plus",
            "must_yield": "positive-sector field equation with K_plus and determinant/source factors",
            "passed": False,
        },
        {
            "variation": "delta S / delta g_minus",
            "must_yield": "negative-sector field equation with K_minus and mirror determinant/source factors",
            "passed": False,
        },
        {
            "variation": "delta S / delta L",
            "must_yield": "transport equation for F_alpha=(D_alpha L)L^{-1} or algebraic constraint fixing L",
            "passed": False,
        },
        {
            "variation": "diagonal diffeomorphism Noether identity",
            "must_yield": "R_plus=0 and R_minus=0 with the same K/L/Q_cross data",
            "passed": False,
        },
    ]
    rejection_conditions = [
        "reject if S_couple is chosen to fit lensing or growth residuals",
        "reject if Q_cross is varied or fitted independently from L",
        "reject if the Lorentz constraint replaces the missing delta S/delta L equation",
        "reject if Noether gives only one combined divergence rather than both sector residuals",
    ]
    minimal_scouple_ansatz = {
        "density": (
            "sqrt(-g_plus) Phi(I_1,I_2,J_matter) + sqrt(-g_minus) Phi_bar(I_1,I_2,J_matter)"
        ),
        "invariants": [
            "I_1=tr(g_plus^{-1} L^T g_minus L)",
            "I_2=det(L)",
            "J_matter=contract(T_plus, L*T_minus*L^T)",
        ],
        "why_minimal": [
            "uses only both metrics, one cross map L, and matter tensors",
            "can vary with respect to g_plus, g_minus, and L",
            "keeps Q_cross tied to the same L",
        ],
        "source_status": "not found in Janus sources; ansatz only",
    }
    symbolic_variation_obligations = [
        {
            "object": "K_plus^{mu nu}",
            "definition": "-2/sqrt(-g_plus) delta S_couple/delta g_plus_{mu nu}",
            "must_match": "positive-sector interaction tensor in the field equation",
            "closed": False,
        },
        {
            "object": "K_minus^{mu nu}",
            "definition": "-2/sqrt(-g_minus) delta S_couple/delta g_minus_{mu nu}",
            "must_match": "negative-sector interaction tensor in the mirror field equation",
            "closed": False,
        },
        {
            "object": "E_L",
            "definition": "delta S_couple/delta L",
            "must_match": "transport or algebraic equation fixing F_alpha=(D_alpha L)L^{-1}",
            "closed": False,
        },
        {
            "object": "Noether diagonal identity",
            "definition": "delta_xi S_couple=0",
            "must_match": "two residual equations, not only one summed conservation law",
            "closed": False,
        },
    ]
    math_result = {
        "can_produce_two_metric_variations": True,
        "can_tie_qcross_to_l": True,
        "can_force_two_residuals_without_extra_structure": False,
        "reason": (
            "diagonal diffeomorphism invariance generically gives one combined Noether identity; "
            "two separate residual closures require an additional source-derived split, mirror "
            "symmetry, or independent sector gauge identity"
        ),
    }
    return {
        "description": "Attempted auxiliary-L action route for deriving Janus transport closure.",
        "status": "auxiliary-action-ansatz-open",
        "action_written_as_ansatz": True,
        "source_derived_action_found": False,
        "new_axiom_risk": True,
        "physics_closed": False,
        "prediction_ready": False,
        "ansatz_terms": ansatz_terms,
        "minimal_scouple_ansatz": minimal_scouple_ansatz,
        "variational_tests": variational_tests,
        "symbolic_variation_obligations": symbolic_variation_obligations,
        "math_result": math_result,
        "rejection_conditions": rejection_conditions,
        "candidate_acceptance": [
            "find S_couple in Janus sources or explicitly label it a new axiom",
            "derive K_plus and K_minus by variation, not by postulated tensors",
            "derive F=D L or a valid algebraic L constraint from delta S/delta L",
            "derive Q_cross from the same L used in K transport",
            "prove the Noether identity implies both residual equations",
        ],
        "verdict": (
            "The minimal S_couple ansatz can define K_plus, K_minus, and keep Q_cross "
            "tied to L. It still does not mathematically force both residuals without "
            "an additional source-derived split identity, so it remains an ansatz."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Auxiliary L Action Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Action written as ansatz: {payload['action_written_as_ansatz']}",
        f"Source-derived action found: {payload['source_derived_action_found']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Ansatz Terms",
        "",
    ]
    for row in payload["ansatz_terms"]:
        lines.append(f"- `{row['term']}`: {row['role']} ({row['source_status']})")
    minimal = payload["minimal_scouple_ansatz"]
    lines.extend(["", "## Minimal S_couple Ansatz", ""])
    lines.append(f"Density: `{minimal['density']}`")
    lines.append(f"Source status: {minimal['source_status']}")
    lines.extend(f"- invariant: `{item}`" for item in minimal["invariants"])
    lines.extend(f"- minimality: {item}" for item in minimal["why_minimal"])
    lines.extend(["", "## Variational Tests", ""])
    for row in payload["variational_tests"]:
        lines.append(f"- `{row['variation']}` -> {row['must_yield']}; passed={row['passed']}")
    lines.extend(["", "## Symbolic Variation Obligations", ""])
    for row in payload["symbolic_variation_obligations"]:
        lines.append(
            f"- `{row['object']}` = `{row['definition']}` -> {row['must_match']}; closed={row['closed']}"
        )
    result = payload["math_result"]
    lines.extend(
        [
            "",
            "## Mathematical Result",
            "",
            f"Can produce two metric variations: {result['can_produce_two_metric_variations']}",
            f"Can tie Q_cross to L: {result['can_tie_qcross_to_l']}",
            (
                "Can force two residuals without extra structure: "
                f"{result['can_force_two_residuals_without_extra_structure']}"
            ),
            f"Reason: {result['reason']}",
        ]
    )
    lines.extend(["", "## Rejection Conditions", ""])
    lines.extend(f"- {item}" for item in payload["rejection_conditions"])
    lines.extend(["", "## Candidate Acceptance", ""])
    lines.extend(f"- {item}" for item in payload["candidate_acceptance"])
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
