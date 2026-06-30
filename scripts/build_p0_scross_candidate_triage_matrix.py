from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_pt_lie_vjanus_ajanus_constraint_solver import (
    build_payload as build_pt_lie_constraints,
)
from scripts.build_p0_ajanus_branch_selector_dynamics_gate import (
    build_payload as build_ajanus_branch_gate,
)
from scripts.build_p0_ajanus_linear_residual_matching_gate import (
    build_payload as build_linear_matching,
)


REPORT_PATH = Path("outputs/reports/p0_scross_candidate_triage_matrix.md")
JSON_PATH = Path("outputs/reports/p0_scross_candidate_triage_matrix.json")


def euler_lagrange(lagrangian: sp.Expr, field: sp.Expr, variable: sp.Symbol) -> sp.Expr:
    velocity = sp.diff(field, variable)
    return sp.simplify(sp.diff(sp.diff(lagrangian, velocity), variable) - sp.diff(lagrangian, field))


def build_symbolic_rows() -> list[dict]:
    t = sp.symbols("t")
    k = sp.symbols("k", positive=True)
    q = sp.Function("q")(t)
    lam = sp.Function("lambda")(t)
    a = sp.Function("a")
    u_free = sp.Function("U_free")
    v_janus = sp.Function("V_Janus")
    a_janus = sp.Function("A_Janus")
    qdot = sp.diff(q, t)

    pure_pullback = a(q) * qdot
    free_potential = -u_free(q)
    wrong_sign = -k * qdot**2 / 2 - u_free(q)
    source_derivative = k * qdot**2 / 2 - v_janus(q)
    bf_constraint = lam * (qdot - a_janus(q))

    rows = [
        {
            "candidate": "pure_pullback_top_form",
            "lagrangian": str(pure_pullback),
            "euler_lagrange_q": str(euler_lagrange(pure_pullback, q, t)),
            "has_transport": False,
            "source_anchored": False,
            "ghost_gate": "not applicable",
            "verdict": "reject: total derivative/passive pullback cannot select phi/L",
        },
        {
            "candidate": "free_ultralocal_potential",
            "lagrangian": str(free_potential),
            "euler_lagrange_q": str(euler_lagrange(free_potential, q, t)),
            "has_transport": False,
            "source_anchored": False,
            "ghost_gate": "not applicable",
            "verdict": "reject unless U_free is source-derived; otherwise it is hand-selected",
        },
        {
            "candidate": "wrong_sign_derivative_solder",
            "lagrangian": str(wrong_sign),
            "euler_lagrange_q": str(euler_lagrange(wrong_sign, q, t)),
            "has_transport": True,
            "source_anchored": False,
            "ghost_gate": "fail: negative kinetic coefficient",
            "verdict": "reject: transport exists but ghost/stability gate fails",
        },
        {
            "candidate": "source_derivative_solder",
            "lagrangian": str(source_derivative),
            "euler_lagrange_q": str(euler_lagrange(source_derivative, q, t)),
            "has_transport": True,
            "source_anchored": True,
            "ghost_gate": "conditional pass if k>0 and V_Janus''>=0 on the branch",
            "verdict": "minimal viable class if V_Janus is forced by Janus source/action",
        },
        {
            "candidate": "bf_source_constraint",
            "lagrangian": str(bf_constraint),
            "euler_lagrange_q": str(euler_lagrange(bf_constraint, q, t)),
            "euler_lagrange_lambda": str(euler_lagrange(bf_constraint, lam, t)),
            "has_transport": True,
            "source_anchored": True,
            "ghost_gate": "constraint system; run Dirac/gauge constraint analysis before acceptance",
            "verdict": "minimal viable class if A_Janus and constraint algebra are source-derived",
        },
    ]
    return rows


def build_payload() -> dict:
    rows = build_symbolic_rows()
    pt_lie = build_pt_lie_constraints()
    branch_gate = build_ajanus_branch_gate()
    linear_matching = build_linear_matching()
    viable = [
        row["candidate"]
        for row in rows
        if row["candidate"] in {"source_derivative_solder", "bf_source_constraint"}
    ]
    rejected = [
        row["candidate"]
        for row in rows
        if row["candidate"]
        in {"pure_pullback_top_form", "free_ultralocal_potential", "wrong_sign_derivative_solder"}
    ]
    return {
        "description": "Symbolic triage matrix for candidate Janus S_cross closure families.",
        "status": "search-space-reduced-physics-open",
        "rows": rows,
        "rejected_families": rejected,
        "minimal_viable_families": viable,
        "pt_lie_constraints": {
            "v_allowed_shape": pt_lie["v_allowed_shape"],
            "a_p_branch_allowed_shape": pt_lie["a_p_branch_allowed_shape"],
            "a_pt_branch_allowed_shape": pt_lie["a_pt_branch_allowed_shape"],
            "branch_selected_by_janus_source": pt_lie["branch_selected_by_janus_source"],
            "coefficients_source_fixed": pt_lie["coefficients_source_fixed"],
        },
        "conditional_ajanus_branch_gate": {
            "selected_if_linear_transport_required": branch_gate["conditional_selected_branch"],
            "pt_like_passes_linear_gate": branch_gate[
                "nondegenerate_linear_transport_gate"
            ]["pt_like_passes"],
            "janus_source_requires_linear_transport": branch_gate[
                "janus_source_requires_linear_transport"
            ],
            "weakfield_linear_matching_selects_p_like": bool(
                linear_matching["janus_source_requires_linear_transport"]
                and not linear_matching["pt_like_can_match_nonzero_linear_residual"]
            ),
        },
        "notable_improvement": (
            "The S_cross search is narrowed to two non-rustine families: a "
            "source-derived derivative solder action, or a source-derived BF/constraint "
            "transport action. Pure pullback, free ultralocal potential, and wrong-sign "
            "derivative solder are eliminated. PT/Lie parity further restricts "
            "V_Janus/A_Janus before fitting."
        ),
        "required_next_proofs": [
            "extract V_Janus or A_Janus from Janus PT/Lie/source equations",
            "lift toy q(t) to covariant phi/L/Omega fields",
            "prove split Noether identities for R_plus=0 and R_minus=0",
            "run ghost/stability or Dirac constraint analysis on the lifted action",
            "bind one same L to K_plus, K_minus, Q_cross, optics and Vlasov",
        ],
        "free_choice_allowed": False,
        "uses_observational_fit": False,
        "prediction_ready": False,
        "verdict": (
            "This is the first actionable filter for S_cross: future work should not "
            "search arbitrary couplings. It should try to source-derive V_Janus or "
            "A_Janus and then lift one of the two viable families covariantly."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 S_cross Candidate Triage Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Minimal viable families: {', '.join(payload['minimal_viable_families'])}",
        f"Rejected families: {', '.join(payload['rejected_families'])}",
        f"Free choice allowed: {payload['free_choice_allowed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Notable Improvement",
        "",
        payload["notable_improvement"],
        "",
        "## PT/Lie Constraints",
        "",
        f"- V allowed shape: `{payload['pt_lie_constraints']['v_allowed_shape']}`",
        f"- A P-like allowed shape: `{payload['pt_lie_constraints']['a_p_branch_allowed_shape']}`",
        f"- A PT-like allowed shape: `{payload['pt_lie_constraints']['a_pt_branch_allowed_shape']}`",
        f"- Branch selected by Janus source: {payload['pt_lie_constraints']['branch_selected_by_janus_source']}",
        f"- Coefficients source fixed: {payload['pt_lie_constraints']['coefficients_source_fixed']}",
        f"- Conditional A branch if linear transport required: `{payload['conditional_ajanus_branch_gate']['selected_if_linear_transport_required']}`",
        f"- PT-like passes linear gate: {payload['conditional_ajanus_branch_gate']['pt_like_passes_linear_gate']}",
        f"- Janus source requires linear transport: {payload['conditional_ajanus_branch_gate']['janus_source_requires_linear_transport']}",
        f"- Weak-field linear matching selects P-like: {payload['conditional_ajanus_branch_gate']['weakfield_linear_matching_selects_p_like']}",
        "",
        "## Candidate Rows",
        "",
        "| candidate | EL(q) | transport | source anchored | ghost gate | verdict |",
        "|---|---|---:|---:|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            "| {candidate} | `{el}` | {transport} | {source} | {ghost} | {verdict} |".format(
                candidate=row["candidate"],
                el=row["euler_lagrange_q"],
                transport=row["has_transport"],
                source=row["source_anchored"],
                ghost=row["ghost_gate"],
                verdict=row["verdict"],
            )
        )
    lines.extend(["", "## Required Next Proofs", ""])
    lines.extend(f"- {item}" for item in payload["required_next_proofs"])
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
