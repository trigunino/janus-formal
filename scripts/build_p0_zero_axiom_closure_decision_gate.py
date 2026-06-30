from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_indirect_path_rule_source_audit import build_payload as build_indirect
from scripts.build_p0_route_c_action_noether_path_rule_derivation_attempt import (
    build_payload as build_action_noether,
)
from scripts.build_p0_route_c_no_path_rule_underselection_theorem import (
    build_payload as build_path_theorem,
)
from scripts.build_p0_route_c_pt_geometry_path_rule_audit import (
    build_payload as build_pt_audit,
)
from scripts.build_p0_route_c_pt_selector_derivation_attempt import (
    build_payload as build_pt_selector,
)
from scripts.build_p0_route_c_pt_only_no_selector_certificate import (
    build_payload as build_pt_no_selector,
)
from scripts.build_p0_route_c_ordered_path_action_source_derivation_gate import (
    build_payload as build_ordered_path_source,
)
from scripts.build_p0_route_c_minimal_spath_extension_axiom_gate import (
    build_payload as build_minimal_spath,
)
from scripts.build_p0_route_c_spath_euler_lagrange_equations import (
    build_payload as build_spath_el,
)
from scripts.build_p0_route_c_spath_lorentz_tetrad_variation_gate import (
    build_payload as build_spath_lorentz,
)
from scripts.build_p0_route_c_spath_same_l_substitution_gate import (
    build_payload as build_spath_same_l,
)
from scripts.build_p0_route_c_spath_stability_screen import (
    build_payload as build_spath_stability,
)
from scripts.build_p0_route_c_spath_bianchi_noether_gate import (
    build_payload as build_spath_bianchi_noether,
)
from scripts.build_p0_route_d_stf_no_go_closure_attempt import (
    build_payload as build_stf_no_go,
)
from scripts.build_p0_route_d_stf_operator_construction_obstruction import (
    build_payload as build_stf_obstruction,
)


REPORT_PATH = Path("outputs/reports/p0_zero_axiom_closure_decision_gate.md")
JSON_PATH = Path("outputs/reports/p0_zero_axiom_closure_decision_gate.json")


def build_payload() -> dict:
    path_theorem = build_path_theorem()
    indirect = build_indirect()
    action_noether = build_action_noether()
    pt_audit = build_pt_audit()
    pt_selector = build_pt_selector()
    pt_no_selector = build_pt_no_selector()
    ordered_path_source = build_ordered_path_source()
    minimal_spath = build_minimal_spath()
    spath_el = build_spath_el()
    spath_lorentz = build_spath_lorentz()
    spath_same_l = build_spath_same_l()
    spath_stability = build_spath_stability()
    spath_bianchi_noether = build_spath_bianchi_noether()
    stf = build_stf_obstruction()
    stf_no_go = build_stf_no_go()
    decision_rows = [
        {
            "front": "route_c_direct_geometry",
            "status": "bounded-underselection",
            "zero_axiom_closes": False,
            "remaining": "Janus-derived path rule",
        },
        {
            "front": "route_c_indirect_sources",
            "status": "filters-not-selectors; action/noether obstructed",
            "zero_axiom_closes": False,
            "remaining": "accepted Noether/action path selector",
        },
        {
            "front": "route_c_pt_geometry",
            "status": "PT-only no-selector bounded",
            "zero_axiom_closes": False,
            "remaining": "source-derived PT path functional or boundary law",
        },
        {
            "front": "route_c_ordered_path_sources",
            "status": "M15/M29/M30/M31 bounded no-source result",
            "zero_axiom_closes": False,
            "remaining": "new Janus source or explicit S_path extension",
        },
        {
            "front": "route_c_minimal_spath_extension",
            "status": "explicit extension candidate with formal EL skeleton; not predictive",
            "zero_axiom_closes": False,
            "remaining": "Euler-Lagrange, same-L, Bianchi/Noether and stability gates",
        },
        {
            "front": "route_d_local_pde",
            "status": "source-free/boundary-free no-selector certified",
            "zero_axiom_closes": False,
            "remaining": "source-derived STF operator",
        },
        {
            "front": "route_d_stf_escape",
            "status": "known non-source families excluded; source-derived escape open",
            "zero_axiom_closes": False,
            "remaining": "accepted Janus action/source chain",
        },
    ]
    return {
        "description": (
            "Decision gate for current zero-axiom closure status. It records what "
            "is closed as a no-selector result and what remains open before any "
            "explicit extension may be considered."
        ),
        "status": "zero-axiom-closure-decision-open",
        "decision_rows": decision_rows,
        "route_c_bounded_underselection_closed": bool(path_theorem["bounded_no_go_closed"]),
        "route_c_indirect_source_found": bool(indirect["indirect_path_rule_source_found"]),
        "route_c_action_noether_path_rule_derived": bool(action_noether["action_noether_path_rule_derived"]),
        "route_c_pt_path_rule_selected": bool(pt_audit["pt_path_rule_selected"]),
        "route_c_pt_selector_derivation_closed": bool(pt_selector["zero_axiom_pt_selector_found"]),
        "route_c_pt_only_no_selector_closed": bool(
            pt_no_selector["bounded_pt_only_no_selector_closed"]
        ),
        "route_c_ordered_path_action_source_found": bool(
            ordered_path_source["ordered_path_action_source_found"]
        ),
        "route_c_ordered_path_source_no_go_closed": bool(
            ordered_path_source["bounded_source_no_go_closed"]
        ),
        "route_c_minimal_spath_extension_declared": bool(minimal_spath["new_axiom_declared"]),
        "route_c_minimal_spath_prediction_ready": bool(minimal_spath["prediction_ready"]),
        "route_c_spath_el_formally_derived": bool(spath_el["gamma_el_derived_formally"])
        and bool(spath_el["l_transport_el_derived_formally"]),
        "route_c_spath_el_prediction_ready": bool(spath_el["prediction_ready"]),
        "route_c_spath_lorentz_variation_formalized": bool(
            spath_lorentz["lorentz_constrained_variation_formalized"]
        ),
        "route_c_spath_lorentz_prediction_ready": bool(spath_lorentz["prediction_ready"]),
        "route_c_spath_same_l_contract_written": bool(
            spath_same_l["same_l_substitution_contract_written"]
        ),
        "route_c_spath_same_l_physics_closed": bool(spath_same_l["same_l_stack_physics_closed"]),
        "route_c_spath_stability_screen_written": bool(spath_stability["stability_screen_written"]),
        "route_c_spath_stability_closed": bool(spath_stability["stability_screen_closed"]),
        "route_c_spath_bianchi_noether_gate_written": bool(
            spath_bianchi_noether["combined_noether_identity_written"]
        ),
        "route_c_spath_metric_stress_variation_written": bool(
            spath_bianchi_noether["metric_stress_variation_written"]
        ),
        "route_c_spath_metric_stress_variation_closed": bool(
            spath_bianchi_noether["metric_stress_variation_closed"]
        ),
        "route_c_spath_bianchi_noether_closed": bool(
            spath_bianchi_noether["bianchi_noether_gate_closed"]
        ),
        "route_c_pt_two_path_counterexample_survives": bool(pt_audit["two_path_counterexample_survives_pt"]),
        "route_d_formal_stf_only": bool(stf["formal_stf_operators_exist"])
        and not bool(stf["accepted_janus_derived_stf_operator_exists"]),
        "route_d_known_non_source_stf_excluded": bool(stf_no_go["all_known_non_source_stf_families_excluded"]),
        "route_d_full_stf_no_go_proved": bool(stf_no_go["full_stf_no_go_proved"]),
        "zero_axiom_closure_available": False,
        "new_axiom_adopted": False,
        "extension_needed_for_prediction_if_no_new_source": True,
        "allowed_next_without_axiom": [
            "find a Janus source for the holonomy path rule",
            "derive an accepted Janus STF source/action operator",
            "prove the remaining STF escape impossible",
        ],
        "forbidden_next": [
            "choose a path family by convenience",
            "promote FLRW/background path to perturbed case",
            "use Q_det/Q_cross as absorption factors",
            "fit lensing residuals to select L",
        ],
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Current zero-axiom closure is not available. The work has produced "
            "bounded no-selector results, not a prediction. The only clean next "
            "moves are source discovery/derivation, STF escape closure, or an "
            "explicit extension contract."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Zero-Axiom Closure Decision Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Route C bounded underselection closed: {payload['route_c_bounded_underselection_closed']}",
        f"Route C indirect source found: {payload['route_c_indirect_source_found']}",
        f"Route C action/Noether path rule derived: {payload['route_c_action_noether_path_rule_derived']}",
        f"Route C PT path rule selected: {payload['route_c_pt_path_rule_selected']}",
        f"Route C PT selector derivation closed: {payload['route_c_pt_selector_derivation_closed']}",
        f"Route C PT-only no-selector closed: {payload['route_c_pt_only_no_selector_closed']}",
        f"Route C ordered path action source found: {payload['route_c_ordered_path_action_source_found']}",
        f"Route C ordered path source no-go closed: {payload['route_c_ordered_path_source_no_go_closed']}",
        f"Route C minimal S_path extension declared: {payload['route_c_minimal_spath_extension_declared']}",
        f"Route C minimal S_path prediction ready: {payload['route_c_minimal_spath_prediction_ready']}",
        f"Route C S_path EL formally derived: {payload['route_c_spath_el_formally_derived']}",
        f"Route C S_path EL prediction ready: {payload['route_c_spath_el_prediction_ready']}",
        f"Route C S_path Lorentz variation formalized: {payload['route_c_spath_lorentz_variation_formalized']}",
        f"Route C S_path Lorentz prediction ready: {payload['route_c_spath_lorentz_prediction_ready']}",
        f"Route C S_path same-L contract written: {payload['route_c_spath_same_l_contract_written']}",
        f"Route C S_path same-L physics closed: {payload['route_c_spath_same_l_physics_closed']}",
        f"Route C S_path stability screen written: {payload['route_c_spath_stability_screen_written']}",
        f"Route C S_path stability closed: {payload['route_c_spath_stability_closed']}",
        f"Route C S_path Bianchi/Noether gate written: {payload['route_c_spath_bianchi_noether_gate_written']}",
        f"Route C S_path metric-stress variation written: {payload['route_c_spath_metric_stress_variation_written']}",
        f"Route C S_path metric-stress variation closed: {payload['route_c_spath_metric_stress_variation_closed']}",
        f"Route C S_path Bianchi/Noether closed: {payload['route_c_spath_bianchi_noether_closed']}",
        f"Route C PT two-path counterexample survives: {payload['route_c_pt_two_path_counterexample_survives']}",
        f"Route D formal STF only: {payload['route_d_formal_stf_only']}",
        f"Route D known non-source STF excluded: {payload['route_d_known_non_source_stf_excluded']}",
        f"Route D full STF no-go proved: {payload['route_d_full_stf_no_go_proved']}",
        f"Zero-axiom closure available: {payload['zero_axiom_closure_available']}",
        f"New axiom adopted: {payload['new_axiom_adopted']}",
        f"Extension needed for prediction if no new source: {payload['extension_needed_for_prediction_if_no_new_source']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| front | status | zero-axiom closes | remaining |",
        "|---|---|---:|---|",
    ]
    for row in payload["decision_rows"]:
        lines.append(
            f"| {row['front']} | {row['status']} | {row['zero_axiom_closes']} | "
            f"{row['remaining']} |"
        )
    lines.extend(["", "## Allowed Next Without Axiom", ""])
    lines.extend(f"- {item}" for item in payload["allowed_next_without_axiom"])
    lines.extend(["", "## Forbidden Next", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_next"])
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
