from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_minimal_janus_soldering_principle_candidate import (
    build_payload as build_soldering_candidate,
)
from scripts.build_p0_route_c_spath_constraint_equation_classifier import (
    build_payload as build_constraint_classifier,
)


REPORT_PATH = Path("outputs/reports/p0_orbifold_pt_soldering_candidate.md")
JSON_PATH = Path("outputs/reports/p0_orbifold_pt_soldering_candidate.json")


def build_payload() -> dict:
    soldering = build_soldering_candidate()
    classifier = build_constraint_classifier()
    geometric_objects = [
        {
            "object": "double_cover",
            "symbol": "M_tilde = M_plus disjoint_union M_minus",
            "role": "keeps the two Janus sectors before quotienting",
        },
        {
            "object": "pt_involution",
            "symbol": "tau: M_tilde -> M_tilde, tau^2=id",
            "role": "exchanges sectors and reverses PT/time orientation labels",
        },
        {
            "object": "orbifold_quotient",
            "symbol": "M_orb = M_tilde / tau",
            "role": "turns PT pairing into geometry rather than a chosen path rule",
        },
        {
            "object": "pt_fixed_locus",
            "symbol": "Sigma_PT = Fix(tau) or defect/throat set",
            "role": "candidate source for boundary and transition data",
        },
        {
            "object": "solder_connection",
            "symbol": "A_PT on the cross-sector frame bundle",
            "role": "single primitive whose holonomy defines L",
        },
        {
            "object": "solder_holonomy",
            "symbol": "L_gamma = P exp integral_gamma A_PT",
            "role": "same-L bridge for K, Q_cross, Vlasov and mirror inverse",
        },
        {
            "object": "orbifold_curvature",
            "symbol": "F_PT = dA_PT + A_PT wedge A_PT plus defect terms",
            "role": "source of C_J/V_J invariant candidates",
        },
    ]
    induced_targets = [
        {
            "target": "S_path",
            "induced_by": "orbifold Wilson/holonomy action of A_PT",
            "automatic": "conditional",
            "remaining": "need source/action principle for A_PT and admissible path measure",
        },
        {
            "target": "same_L",
            "induced_by": "one holonomy L_gamma from one A_PT",
            "automatic": "yes-if-A_PT-unique",
            "remaining": "prove uniqueness/gauge fixing and mirror inverse",
        },
        {
            "target": "C_J/V_J",
            "induced_by": "local invariants of F_PT, defect curvature, torsion/nonmetricity",
            "automatic": "conditional",
            "remaining": "derive coefficients from orbifold action, not choose them",
        },
        {
            "target": "PT_boundary",
            "induced_by": "Sigma_PT fixed locus or defect matching condition",
            "automatic": "conditional",
            "remaining": "prove Sigma_PT dynamics or boundary variation",
        },
        {
            "target": "Bianchi_Noether",
            "induced_by": "orbifold-covariant action variation",
            "automatic": "no",
            "remaining": "derive split sector identities R_plus=0 and R_minus=0",
        },
    ]
    acceptance_gates = [
        "write a covariant orbifold action S_orb[g_plus,g_minus,A_PT,tau]",
        "derive A_PT Euler equation and boundary condition on Sigma_PT",
        "prove L_gamma from A_PT is the same L used by K, Q_cross and Vlasov",
        "derive C_J/V_J coefficients from F_PT or defect terms",
        "prove split Noether/Bianchi identities, not only diagonal covariance",
        "run ghost/tachyon and caustic/multibranch stability screens",
        "forbid observational fit and Q_det/Q_cross scalar absorption",
    ]
    return {
        "description": (
            "Orbifold/PT soldering candidate: replace an added S_path by one "
            "geometric primitive, a PT orbifold quotient with a solder connection."
        ),
        "status": "orbifold-pt-soldering-candidate-not-source-derived",
        "depends_on": [
            "p0_minimal_janus_soldering_principle_candidate",
            "p0_route_c_spath_constraint_equation_classifier",
        ],
        "soldering_candidate_status": soldering["status"],
        "constraint_classifier_status": classifier["status"],
        "geometric_objects": geometric_objects,
        "induced_targets": induced_targets,
        "acceptance_gates": acceptance_gates,
        "single_geometric_primitive": "PT orbifold solder connection A_PT",
        "motivating_geometry": [
            "Sakharov twin-universe opposite time arrows",
            "PT/T-symmetry and energy/mass sign reversal",
            "two-fold cover / Mobius-Boy / projective-space intuition",
            "orbifold quotient with fixed/defect locus Sigma_PT",
        ],
        "new_axiom_candidate": True,
        "source_derived_from_published_janus": False,
        "less_rustine_than_free_spath": True,
        "s_path_added_by_hand": False,
        "same_l_made_structural": True,
        "cj_vj_still_need_action_coefficients": True,
        "orbifold_action_written": False,
        "a_pt_euler_equation_derived": False,
        "split_noether_bianchi_proved": False,
        "stability_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is the cleanest extension direction found so far: one PT-orbifold "
            "solder connection could induce S_path, same-L and C_J/V_J together. "
            "It is not yet Janus closure because the orbifold action, A_PT equation, "
            "defect boundary law, coefficients, split Noether and stability gates "
            "remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Orbifold/PT Soldering Candidate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Single geometric primitive: `{payload['single_geometric_primitive']}`",
        f"New axiom candidate: {payload['new_axiom_candidate']}",
        f"Source-derived from published Janus: {payload['source_derived_from_published_janus']}",
        f"Less rustine than free S_path: {payload['less_rustine_than_free_spath']}",
        f"S_path added by hand: {payload['s_path_added_by_hand']}",
        f"Same-L made structural: {payload['same_l_made_structural']}",
        f"C_J/V_J still need action coefficients: {payload['cj_vj_still_need_action_coefficients']}",
        f"Orbifold action written: {payload['orbifold_action_written']}",
        f"A_PT Euler equation derived: {payload['a_pt_euler_equation_derived']}",
        f"Split Noether/Bianchi proved: {payload['split_noether_bianchi_proved']}",
        f"Stability closed: {payload['stability_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Motivating Geometry",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["motivating_geometry"])
    lines.extend(["", "## Geometric Objects", "", "| object | symbol | role |", "|---|---|---|"])
    for row in payload["geometric_objects"]:
        lines.append(f"| {row['object']} | `{row['symbol']}` | {row['role']} |")
    lines.extend(["", "## Induced Targets", "", "| target | induced by | automatic | remaining |", "|---|---|---|---|"])
    for row in payload["induced_targets"]:
        lines.append(
            f"| {row['target']} | {row['induced_by']} | {row['automatic']} | {row['remaining']} |"
        )
    lines.extend(["", "## Acceptance Gates", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_gates"])
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
