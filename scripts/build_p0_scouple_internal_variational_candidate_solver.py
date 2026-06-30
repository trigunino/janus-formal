from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_scouple_internal_variational_candidate_solver.md")
JSON_PATH = Path("outputs/reports/p0_scouple_internal_variational_candidate_solver.json")


def build_payload() -> dict:
    i_metric, d, c0, c1, c2, c3 = sp.symbols("I_metric d c0 c1 c2 c3")
    phi = c0 + c1 * (i_metric - d) + c2 * (i_metric - d) ** 2 + c3 * (i_metric - d) ** 3
    dphi = sp.diff(phi, i_metric)
    aligned = {i_metric: d}
    stationarity_solution = sp.solve([dphi.subs(aligned)], [c1], dict=True)
    zero_vacuum_solution = sp.solve([phi.subs(aligned)], [c0], dict=True)
    combined_solution = sp.solve([phi.subs(aligned), dphi.subs(aligned)], [c0, c1], dict=True)

    s0, s1, l0, l1 = sp.symbols("s0 s1 l0 l1")
    i_from_l = s0 * l0**2 + s1 * l1**2
    phi_l = phi.subs({i_metric: i_from_l, d: 2})
    e_l0 = sp.factor(sp.diff(phi_l, l0))
    e_l1 = sp.factor(sp.diff(phi_l, l1))
    aligned_l = {s0: 1, s1: 1, l0: 1, l1: 1}
    e_l_aligned = [
        str(sp.simplify(e_l0.subs(aligned_l))),
        str(sp.simplify(e_l1.subs(aligned_l))),
    ]
    e_l_after_constraints = [
        str(sp.simplify(e_l0.subs(aligned_l).subs({c1: 0}))),
        str(sp.simplify(e_l1.subs(aligned_l).subs({c1: 0}))),
    ]

    acceptance_checks = [
        {
            "check": "aligned_stationarity",
            "result": "forces c1=0",
            "closed": True,
        },
        {
            "check": "zero_aligned_vacuum_energy",
            "result": "forces c0=0",
            "closed": True,
        },
        {
            "check": "unique_local_phi",
            "result": "c2 and c3 remain free even in this cubic truncation",
            "closed": False,
        },
        {
            "check": "L_transport",
            "result": "delta S/delta L gives algebraic extremum equations, not D L transport",
            "closed": False,
        },
        {
            "check": "split_noether",
            "result": "local scalar action gives diagonal Noether identity unless extra sector split is added",
            "closed": False,
        },
        {
            "check": "pressure_pi",
            "result": "pressure/Pi need matter action and tensor stress response, not only Phi(I_metric)",
            "closed": False,
        },
    ]
    return {
        "description": "Internal symbolic attempt to derive an accepted local S_couple candidate without source lookup.",
        "status": "internal-variational-candidate-open",
        "candidate_family": "Phi=c0+c1*(I_metric-d)+c2*(I_metric-d)^2+c3*(I_metric-d)^3",
        "phi": str(phi),
        "dphi_dimetric": str(dphi),
        "stationarity_solution": str(stationarity_solution),
        "zero_vacuum_solution": str(zero_vacuum_solution),
        "combined_solution": str(combined_solution),
        "remaining_free_coefficients_after_basic_closure": ["c2", "c3"],
        "e_l0": str(e_l0),
        "e_l1": str(e_l1),
        "e_l_aligned": e_l_aligned,
        "e_l_after_constraints": e_l_after_constraints,
        "acceptance_checks": acceptance_checks,
        "aligned_branch_stationary": True,
        "zero_vacuum_energy_fixed": True,
        "unique_phi_forced": False,
        "el_is_transport_equation": False,
        "split_noether_closed": False,
        "pressure_pi_closed": False,
        "uses_observational_fit": False,
        "accepted_scouple_action_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The internal derivation improves the obstruction: basic variational consistency "
            "kills c0 and c1 but leaves higher local coefficients free. The L equation is "
            "algebraic, not a D L transport law, and pressure/Pi plus split Noether remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 S_couple Internal Variational Candidate Solver",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate family: `{payload['candidate_family']}`",
        f"Stationarity solution: `{payload['stationarity_solution']}`",
        f"Zero vacuum solution: `{payload['zero_vacuum_solution']}`",
        f"Combined solution: `{payload['combined_solution']}`",
        f"Remaining free coefficients: {', '.join(payload['remaining_free_coefficients_after_basic_closure'])}",
        f"Unique Phi forced: {payload['unique_phi_forced']}",
        f"E_L is transport equation: {payload['el_is_transport_equation']}",
        f"Split Noether closed: {payload['split_noether_closed']}",
        f"Pressure/Pi closed: {payload['pressure_pi_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Accepted S_couple action found: {payload['accepted_scouple_action_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## L Variation",
        "",
        f"- E_l0: `{payload['e_l0']}`",
        f"- E_l1: `{payload['e_l1']}`",
        f"- aligned: `{payload['e_l_aligned']}`",
        f"- after constraints: `{payload['e_l_after_constraints']}`",
        "",
        "## Acceptance Checks",
        "",
        "| check | result | closed |",
        "|---|---|---:|",
    ]
    for row in payload["acceptance_checks"]:
        lines.append(f"| {row['check']} | {row['result']} | {row['closed']} |")
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
