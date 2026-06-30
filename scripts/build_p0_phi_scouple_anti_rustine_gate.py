from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_auxiliary_l_action_attempt import build_payload as build_auxiliary_l_action
from scripts.build_p0_scouple_internal_variational_candidate_solver import (
    build_payload as build_internal_solver,
)
from scripts.build_p0_scouple_matter_invariant_solver import build_payload as build_matter_solver
from scripts.build_p0_scouple_accepted_action_search import build_payload as build_scouple_search
from scripts.build_p0_split_noether_calculable_target import build_payload as build_split_noether
from scripts.build_p0_stueckelberg_explicit_action_test import build_payload as build_explicit_action
from scripts.build_p0_stueckelberg_mirror_phi_constraints import (
    build_payload as build_mirror_phi_constraints,
)
from scripts.build_p0_variational_closure_route import build_payload as build_variational_route


REPORT_PATH = Path("outputs/reports/p0_phi_scouple_anti_rustine_gate.md")
JSON_PATH = Path("outputs/reports/p0_phi_scouple_anti_rustine_gate.json")


def build_payload() -> dict:
    auxiliary = build_auxiliary_l_action()
    internal_solver = build_internal_solver()
    matter_solver = build_matter_solver()
    scouple_search = build_scouple_search()
    explicit = build_explicit_action()
    mirror = build_mirror_phi_constraints()
    split = build_split_noether()
    variational = build_variational_route()

    constraint_tests = [
        {
            "constraint": "M15 determinant cross-source factors",
            "effect": "fixes B_4vol source weights",
            "uniqueness_power": "partial",
        },
        {
            "constraint": "plus/minus mirror symmetry",
            "effect": "fixes Phi_bar once Phi is chosen",
            "uniqueness_power": "partial",
        },
        {
            "constraint": "same L for K transport and Q_cross",
            "effect": "forbids independent optical and matter maps",
            "uniqueness_power": "partial",
        },
        {
            "constraint": "Newtonian sign recovery",
            "effect": "filters sign and normalization branches",
            "uniqueness_power": "partial",
        },
        {
            "constraint": "no observational fit constants",
            "effect": "blocks data-tuned corrections",
            "uniqueness_power": "negative-only",
        },
        {
            "constraint": "split Noether R_plus=R_minus=0",
            "effect": "required closure test after a candidate Phi is chosen",
            "uniqueness_power": "not-yet-proved",
        },
    ]
    family_obstruction = [
        "functions of admissible scalar invariants can satisfy mirror and no-fit rules",
        "field-source determinant factors fix cross-source weights but not the full variational potential",
        "Lorentz admissibility of L constrains the map but does not select one map equation",
        "weak-field sign recovery filters branches but does not fix nonlinear terms",
    ]
    anti_rustine_rules = [
        "do not adopt A_phi_scouple until constraints force a unique candidate or an explicit new-axiom label is accepted",
        "do not use observations to choose Phi coefficients or branches",
        "do not call Janus published-closed if Phi/S_couple is introduced by this project",
        "do not unlock prediction_ready while family_obstruction remains true",
    ]
    variational_acceptance_rows = [
        {
            "check": "source_supplied_action",
            "required": "Janus source supplies S_couple or an explicit new axiom is deliberately adopted",
            "local_shape_available": bool(auxiliary["action_written_as_ansatz"] and explicit["action_written"]),
            "accepted": bool(scouple_search["independent_scouple_found"]),
        },
        {
            "check": "metric_variations",
            "required": "delta S_couple/delta g_plus and delta S_couple/delta g_minus derive K_plus/K_minus",
            "local_shape_available": bool(auxiliary["math_result"]["can_produce_two_metric_variations"]),
            "accepted": all(row["passed"] for row in auxiliary["variational_tests"][:2]),
        },
        {
            "check": "same_l_qcross",
            "required": "the same L defines K transport and Q_cross",
            "local_shape_available": bool(
                auxiliary["math_result"]["can_tie_qcross_to_l"]
                and mirror["same_l_for_k_and_qcross"]
            ),
            "accepted": bool(explicit["source_derived"] and mirror["source_derived"]),
        },
        {
            "check": "split_noether",
            "required": "split Noether identities prove both R_plus=0 and R_minus=0",
            "local_shape_available": bool(split["split_noether_identities_written"]),
            "accepted": bool(split["split_noether_identities_proved"]),
        },
        {
            "check": "no_fit",
            "required": "no fitted potential, optical amplitude, or survey-normalized coefficient",
            "local_shape_available": True,
            "accepted": bool(not variational["allows_fitted_potentials"]),
        },
        {
            "check": "pressure_pi_extension",
            "required": "pressure and anisotropic stress are derived or non-dust claims stay blocked",
            "local_shape_available": True,
            "accepted": bool(
                matter_solver["pressure_coefficient_source_fixed"]
                and matter_solver["pi_coefficient_source_fixed"]
            ),
        },
    ]
    variational_acceptance_gate_passed = all(row["accepted"] for row in variational_acceptance_rows)
    return {
        "description": "Anti-rustine gate for A_phi_scouple: forced derivation versus free completion.",
        "status": "not-forced-family-remains-open",
        "constraint_tests": constraint_tests,
        "variational_acceptance_rows": variational_acceptance_rows,
        "accepted_action_search_status": scouple_search["status"],
        "closest_published_action": scouple_search["closest_published_action"],
        "m15_action_accepted_as_scouple": scouple_search["m15_action_accepted_as_scouple"],
        "internal_variational_solver_status": internal_solver["status"],
        "internal_solver_unique_phi_forced": internal_solver["unique_phi_forced"],
        "internal_solver_el_is_transport_equation": internal_solver["el_is_transport_equation"],
        "matter_invariant_solver_status": matter_solver["status"],
        "matter_solver_pressure_fixed": matter_solver["pressure_coefficient_source_fixed"],
        "matter_solver_pi_fixed": matter_solver["pi_coefficient_source_fixed"],
        "family_obstruction": family_obstruction,
        "anti_rustine_rules": anti_rustine_rules,
        "local_variational_shapes_available": any(
            row["local_shape_available"] for row in variational_acceptance_rows
        ),
        "variational_acceptance_gate_passed": variational_acceptance_gate_passed,
        "constraints_force_unique_phi_scouple": False,
        "multiple_no_fit_candidates_remain_possible": True,
        "can_adopt_as_published_janus_derivation": False,
        "can_adopt_only_as_explicit_new_axiom": True,
        "new_axiom_adopted": False,
        "forced_selection_search_available": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A_phi_scouple is not forced by the current constraints. It is not an admissible "
            "published-Janus closure: local variational shapes exist, but source action, "
            "metric variations, same-L source derivation, split Noether closure, and "
            "pressure/Pi extension are not all accepted."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Phi/S_couple Anti-Rustine Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Local variational shapes available: {payload['local_variational_shapes_available']}",
        f"Variational acceptance gate passed: {payload['variational_acceptance_gate_passed']}",
        f"Accepted action search status: {payload['accepted_action_search_status']}",
        f"Closest published action: {payload['closest_published_action']}",
        f"M15 action accepted as S_couple: {payload['m15_action_accepted_as_scouple']}",
        f"Internal variational solver status: {payload['internal_variational_solver_status']}",
        f"Internal solver unique Phi forced: {payload['internal_solver_unique_phi_forced']}",
        f"Internal solver E_L is transport equation: {payload['internal_solver_el_is_transport_equation']}",
        f"Matter invariant solver status: {payload['matter_invariant_solver_status']}",
        f"Matter solver pressure fixed: {payload['matter_solver_pressure_fixed']}",
        f"Matter solver Pi fixed: {payload['matter_solver_pi_fixed']}",
        f"Constraints force unique Phi/S_couple: {payload['constraints_force_unique_phi_scouple']}",
        f"Multiple no-fit candidates remain possible: {payload['multiple_no_fit_candidates_remain_possible']}",
        f"Can adopt as published Janus derivation: {payload['can_adopt_as_published_janus_derivation']}",
        f"Can adopt only as explicit new axiom: {payload['can_adopt_only_as_explicit_new_axiom']}",
        f"New axiom adopted: {payload['new_axiom_adopted']}",
        f"Forced selection search available: {payload['forced_selection_search_available']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Constraint Tests",
        "",
        "| constraint | effect | uniqueness power |",
        "|---|---|---|",
    ]
    for row in payload["constraint_tests"]:
        lines.append(f"| {row['constraint']} | {row['effect']} | {row['uniqueness_power']} |")
    lines.extend(
        [
            "",
            "## Variational Acceptance Gate",
            "",
            "| check | required | local shape available | accepted |",
            "|---|---|---:|---:|",
        ]
    )
    for row in payload["variational_acceptance_rows"]:
        lines.append(
            f"| {row['check']} | {row['required']} | "
            f"{row['local_shape_available']} | {row['accepted']} |"
        )
    lines.extend(["", "## Family Obstruction", ""])
    lines.extend(f"- {item}" for item in payload["family_obstruction"])
    lines.extend(["", "## Anti-Rustine Rules", ""])
    lines.extend(f"- {item}" for item in payload["anti_rustine_rules"])
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
