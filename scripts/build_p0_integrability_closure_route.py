from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_integrability_closure_route.md")
JSON_PATH = Path("outputs/reports/p0_integrability_closure_route.json")


def build_payload() -> dict:
    relative_connection = {
        "object": "Omega_alpha = omega_plus_alpha - L omega_minus_alpha L^{-1} - (D_alpha L) L^{-1}",
        "cartan_tetrad_reading": (
            "Omega is the relative spin/tetrad connection seen by an L-soldered frame; "
            "its curvature R_Omega=d Omega+Omega wedge Omega measures failure of flat "
            "relative transport"
        ),
        "dl_equation": "D_alpha L = -Omega_alpha L plus the chosen sector-connection convention",
        "lorentz_condition": "Omega must be eta-antisymmetric so D_alpha(L^T eta L)=0",
    }
    branch_rules = [
        {
            "branch": "flat_pure_gauge",
            "condition": "R_Omega=0 on a simply connected patch",
            "local_result": "Frobenius integrability lets L be solved locally from initial Lorentz data",
            "global_result": "global L is path-independent only when holonomy is trivial",
            "path_rule": "no independent path rule is needed after source-derived flatness is proved",
        },
        {
            "branch": "flat_nontrivial_holonomy",
            "condition": "R_Omega=0 but pi_1(domain) allows nontrivial representation",
            "local_result": "local solutions exist, but global single-valued L needs holonomy constraints",
            "global_result": "loop holonomy classes can change L unless the source fixes or kills the representation",
            "path_rule": "source must derive the allowed loop/monodromy rule before K or Q_cross use",
        },
        {
            "branch": "curved_relative_holonomy",
            "condition": "R_Omega!=0",
            "local_result": "L can be propagated along curves, not promoted to path-independent field data",
            "global_result": "closed loops generate curvature-ordered holonomy constraints",
            "path_rule": "a source-derived curve/family rule is mandatory and must be the same for K and Q_cross",
        },
    ]
    frobenius_checks = [
        "commutator [D_alpha,D_beta]L must match R_Omega action from the declared Cartan connection",
        "R_Omega=0 is the local path-independence condition for the first-order DL system",
        "nonzero R_Omega turns rectangular/loop transport into a curvature/path rule, not a free fit",
        "eta-antisymmetry and initial Lorentz data are required to keep L Lorentz-admissible",
    ]
    closure_obligations = [
        "derive Omega or R_Omega from Janus source equations rather than choosing it phenomenologically",
        "state whether the accepted branch is pure gauge, flat holonomy, or curved holonomy",
        "use the same L and the same path/family rule for Bianchi K and optical Q_cross",
        "prove loop composition consistency before any global prediction claim",
        "verify D(BK)=0 on the same branch after the integrability rule is fixed",
    ]
    return {
        "description": "Bounded P0 route for closing Janus L transport through Cartan integrability.",
        "status": "integrability-closure-route-open",
        "source_derived_curvature_rule": False,
        "source_derived_path_rule": False,
        "same_l_for_k_and_qcross": True,
        "physics_closed": False,
        "prediction_ready": False,
        "relative_connection": relative_connection,
        "branch_rules": branch_rules,
        "frobenius_checks": frobenius_checks,
        "closure_obligations": closure_obligations,
        "verdict": (
            "The differential-geometry route can close L only after Janus sources fix "
            "Omega/R_Omega and the corresponding path or holonomy rule. Flat pure gauge "
            "gives local path-independent L; nontrivial holonomy or R_Omega!=0 requires "
            "loop rules. The branch is not prediction-ready."
        ),
    }


def render_markdown(payload: dict) -> str:
    rel = payload["relative_connection"]
    lines = [
        "# P0 Integrability Closure Route",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source-derived curvature rule: {payload['source_derived_curvature_rule']}",
        f"Source-derived path rule: {payload['source_derived_path_rule']}",
        f"Same L for K and Q_cross: {payload['same_l_for_k_and_qcross']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Relative Connection",
        "",
        f"- Object: `{rel['object']}`",
        f"- Cartan/tetrad reading: {rel['cartan_tetrad_reading']}",
        f"- DL equation: `{rel['dl_equation']}`",
        f"- Lorentz condition: {rel['lorentz_condition']}",
        "",
        "## Branch Rules",
        "",
    ]
    for rule in payload["branch_rules"]:
        lines.extend(
            [
                f"### {rule['branch']}",
                "",
                f"- Condition: `{rule['condition']}`",
                f"- Local result: {rule['local_result']}",
                f"- Global result: {rule['global_result']}",
                f"- Path rule: {rule['path_rule']}",
                "",
            ]
        )
    lines.extend(["## Frobenius/Integrability Checks", ""])
    lines.extend(f"- {item}" for item in payload["frobenius_checks"])
    lines.extend(["", "## Closure Obligations", ""])
    lines.extend(f"- {item}" for item in payload["closure_obligations"])
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
