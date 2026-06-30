from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_ordered_path_action_source_derivation_gate import (
    build_payload as build_ordered_path_source,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_minimal_spath_extension_axiom_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_minimal_spath_extension_axiom_gate.json")


def build_payload() -> dict:
    source_gate = build_ordered_path_source()
    action_terms = [
        {
            "term": "path_selector",
            "schematic": "Integral C_J(g_plus,g_minus,PT; gamma,dgamma) ds",
            "role": "select gamma without survey/lensing fit",
            "accepted": False,
        },
        {
            "term": "lorentz_transport",
            "schematic": "Integral ||D_s L + Gamma_plus L - L Gamma_minus||_eta^2 ds",
            "role": "induce one Lorentz/tetrad-compatible L",
            "accepted": False,
        },
        {
            "term": "pt_mirror_inverse",
            "schematic": "L_minus_to_plus(PT gamma) = inverse(L_plus_to_minus(gamma))",
            "role": "enforce PT/mirror reciprocity",
            "accepted": False,
        },
        {
            "term": "boundary_law",
            "schematic": "B_PT[gamma endpoints; g_plus,g_minus]",
            "role": "fix endpoints/surface covariantly",
            "accepted": False,
        },
    ]
    acceptance_rows = [
        {
            "gate": "declared_extension",
            "requirement": "state S_path is not derived from currently inspected Janus sources",
            "passed": True,
        },
        {
            "gate": "no_fit_no_absorption",
            "requirement": "no observational fit and no Q_det/Q_cross scalar absorption",
            "passed": True,
        },
        {
            "gate": "same_l_stack",
            "requirement": "same L must feed K, Q_cross, Vlasov/matter and mirror inverse",
            "passed": False,
        },
        {
            "gate": "euler_lagrange_equations",
            "requirement": "derive delta_gamma S_path = 0 and delta_L S_path = 0",
            "passed": False,
        },
        {
            "gate": "bianchi_noether_closure",
            "requirement": "close R_plus/R_minus and split Noether residuals",
            "passed": False,
        },
        {
            "gate": "stability_screen",
            "requirement": "pass principal symbol, ghost, tachyon and boundary-mode checks",
            "passed": False,
        },
        {
            "gate": "caustic_multibranch_control",
            "requirement": "define sheet/path behavior through caustics or multistreaming",
            "passed": False,
        },
    ]
    return {
        "description": (
            "Minimal explicit Route C extension axiom for an ordered cross-sector "
            "path action. This is a traceable candidate, not a Janus-source proof "
            "and not a prediction gate."
        ),
        "status": "minimal-spath-extension-axiom-proposed-not-predictive",
        "depends_on": ["p0_route_c_ordered_path_action_source_derivation_gate"],
        "ordered_path_source_status": source_gate["status"],
        "bounded_no_source_result_available": bool(source_gate["bounded_source_no_go_closed"]),
        "extension_object": "S_path[gamma,L; g_plus,g_minus,PT]",
        "extension_is_explicit": True,
        "source_derived_from_published_janus": False,
        "new_axiom_declared": True,
        "new_axiom_adopted_for_prediction": False,
        "minimality_claim": "adds one path/transport action object; no density, lensing or amplitude fit",
        "action_terms": action_terms,
        "acceptance_rows": acceptance_rows,
        "acceptance_passed_count": sum(1 for row in acceptance_rows if row["passed"]),
        "acceptance_required_count": len(acceptance_rows),
        "forbids_observational_fit": True,
        "forbids_qdet_qcross_absorption": True,
        "requires_same_l": True,
        "requires_mirror_inverse": True,
        "requires_bianchi_noether_closure": True,
        "requires_stability": True,
        "can_be_used_for_prediction_now": False,
        "next_required_artifacts": [
            "p0_route_c_spath_euler_lagrange_equations",
            "p0_route_c_spath_lorentz_tetrad_variation_gate",
            "p0_route_c_spath_same_l_substitution_gate",
            "p0_route_c_spath_stability_screen",
            "p0_route_c_spath_bianchi_noether_closure_gate",
        ],
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "S_path is now stated as the minimal clean extension candidate. It is "
            "explicitly not derived from the inspected Janus sources and cannot be "
            "used for prediction until the same-L stack, variational equations, "
            "Bianchi/Noether closure and stability checks pass."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Minimal S_path Extension Axiom Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Extension object: `{payload['extension_object']}`",
        f"Extension is explicit: {payload['extension_is_explicit']}",
        f"Source-derived from published Janus: {payload['source_derived_from_published_janus']}",
        f"New axiom declared: {payload['new_axiom_declared']}",
        f"New axiom adopted for prediction: {payload['new_axiom_adopted_for_prediction']}",
        f"Minimality claim: {payload['minimality_claim']}",
        f"Forbids observational fit: {payload['forbids_observational_fit']}",
        f"Forbids Qdet/Qcross absorption: {payload['forbids_qdet_qcross_absorption']}",
        f"Can be used for prediction now: {payload['can_be_used_for_prediction_now']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Action Terms",
        "",
        "| term | schematic | role | accepted |",
        "|---|---|---|---:|",
    ]
    for row in payload["action_terms"]:
        lines.append(f"| {row['term']} | {row['schematic']} | {row['role']} | {row['accepted']} |")
    lines.extend(["", "## Acceptance Gates", "", "| gate | requirement | passed |", "|---|---|---:|"])
    for row in payload["acceptance_rows"]:
        lines.append(f"| {row['gate']} | {row['requirement']} | {row['passed']} |")
    lines.extend(["", "## Next Required Artifacts", ""])
    lines.extend(f"- `{item}`" for item in payload["next_required_artifacts"])
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
