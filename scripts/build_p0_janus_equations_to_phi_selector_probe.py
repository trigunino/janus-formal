from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_lapse_slice_from_janus_gauge_probe import (
    build_payload as build_lapse_slice_probe,
)


REPORT_PATH = Path("outputs/reports/p0_janus_equations_to_phi_selector_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_equations_to_phi_selector_probe.json")


def build_payload() -> dict:
    lapse_slice = build_lapse_slice_probe()
    epsilon, x, r = sp.symbols("epsilon x r", real=True)
    j_phi = 1 + epsilon * sp.cos(x)
    m15_b_target = r
    lapse_slice_factor = sp.simplify(m15_b_target / j_phi)
    equation_if_unit_lapse_slice = sp.simplify(j_phi - r)
    unit_lapse_slice_solution = sp.solve([equation_if_unit_lapse_slice.subs(x, 0)], [epsilon], dict=True)
    equation_for_all_x_at_r1 = sp.Poly(sp.expand((j_phi - 1)), sp.cos(x))
    selectors = [
        {
            "row": "m15_cross_source_weight",
            "janus_equation_input": "B_4vol=sqrt(-g_source/-g_receiver)",
            "imposes": "the active cross-source 4-volume weight",
            "fixes_phi": False,
        },
        {
            "row": "decomposition_with_free_lapse_slice",
            "janus_equation_input": "B_4vol=J_phi*N_source*sqrt(gamma_source)/(N_receiver*sqrt(gamma_receiver))",
            "imposes": f"lapse_slice_factor={lapse_slice_factor}",
            "fixes_phi": False,
        },
        {
            "row": "extra_unit_lapse_slice_gauge",
            "janus_equation_input": "if additionally N and slice ratio are fixed to 1",
            "imposes": f"J_phi=r; at x=0 gives {unit_lapse_slice_solution}",
            "fixes_phi": True,
        },
        {
            "row": "extra_identity_background",
            "janus_equation_input": "if additionally r=1 and equality holds for all x",
            "imposes": f"polynomial coefficients {equation_for_all_x_at_r1.all_coeffs()} vanish",
            "fixes_phi": True,
        },
    ]
    return {
        "description": "Probe deriving what Janus field-equation source weights impose on phi/J/L selection.",
        "status": "janus-equations-fix-b4vol-not-phi-without-extra-gauge",
        "candidate_family": "phi=x+epsilon sin(x), J=1+epsilon cos(x)",
        "m15_b_target": "B_4vol=sqrt(-g_source/-g_receiver)",
        "lapse_slice_factor_needed": str(lapse_slice_factor),
        "unit_lapse_slice_solution_at_x0": str(unit_lapse_slice_solution),
        "selectors": selectors,
        "janus_equations_select_b4vol_weight": True,
        "janus_equations_select_phi_without_extra_gauge": False,
        "extra_unit_lapse_slice_gauge_selects_phi": True,
        "extra_identity_background_selects_epsilon_zero": True,
        "extra_gauge_source_supplied": False,
        "lapse_slice_probe_status": lapse_slice["status"],
        "proper_time_slicing_can_fix_lapse": lapse_slice["proper_time_slicing_can_fix_lapse"],
        "flrw_comoving_branch_can_fix_lapse_slice": lapse_slice[
            "flrw_comoving_branch_can_fix_lapse_slice"
        ],
        "general_perturbed_branch_lapse_slice_fixed": lapse_slice[
            "general_perturbed_branch_lapse_slice_fixed"
        ],
        "source_derived_phi_selector_found": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "M15-style source equations select the B4vol cross-source weight. They do not "
            "select phi/J/L unless an extra lapse/slice or identity-background gauge is supplied."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Equations To Phi Selector Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate family: `{payload['candidate_family']}`",
        f"M15 B target: `{payload['m15_b_target']}`",
        f"Lapse/slice factor needed: `{payload['lapse_slice_factor_needed']}`",
        f"Unit lapse/slice solution at x=0: `{payload['unit_lapse_slice_solution_at_x0']}`",
        f"Janus equations select B4vol weight: {payload['janus_equations_select_b4vol_weight']}",
        f"Janus equations select phi without extra gauge: {payload['janus_equations_select_phi_without_extra_gauge']}",
        f"Extra unit lapse/slice gauge selects phi: {payload['extra_unit_lapse_slice_gauge_selects_phi']}",
        f"Extra gauge source supplied: {payload['extra_gauge_source_supplied']}",
        f"Lapse/slice probe status: {payload['lapse_slice_probe_status']}",
        f"Proper-time slicing can fix lapse: {payload['proper_time_slicing_can_fix_lapse']}",
        f"FLRW comoving branch can fix lapse/slice: {payload['flrw_comoving_branch_can_fix_lapse_slice']}",
        f"General perturbed branch lapse/slice fixed: {payload['general_perturbed_branch_lapse_slice_fixed']}",
        f"Source-derived phi selector found: {payload['source_derived_phi_selector_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Selectors",
        "",
        "| row | Janus equation input | imposes | fixes phi |",
        "|---|---|---|---:|",
    ]
    for row in payload["selectors"]:
        lines.append(
            f"| {row['row']} | `{row['janus_equation_input']}` | `{row['imposes']}` | "
            f"{row['fixes_phi']} |"
        )
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
