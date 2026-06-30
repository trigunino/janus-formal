from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_d_source_free_pde_nullspace_probe import (
    build_payload as build_pde_probe,
)
from scripts.build_p0_route_d_source_free_boundary_no_go_argument import (
    build_payload as build_no_go,
)


REPORT_PATH = Path("outputs/reports/p0_route_d_derivative_curvature_nullspace_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_d_derivative_curvature_nullspace_gate.json")


def build_payload() -> dict:
    pde_probe = build_pde_probe()
    no_go = build_no_go()
    family_rows = [
        {
            "family": "dl_kinetic",
            "operator_order": 2,
            "free_constants": True,
            "source_rhs_derived": False,
            "boundary_data_derived": False,
            "same_l_split_noether_closed": False,
            "excluded_as_no_axiom_selector": True,
        },
        {
            "family": "massive_dl_kinetic",
            "operator_order": 2,
            "free_constants": True,
            "source_rhs_derived": False,
            "boundary_data_derived": False,
            "same_l_split_noether_closed": False,
            "excluded_as_no_axiom_selector": True,
        },
        {
            "family": "phi_bending",
            "operator_order": 4,
            "free_constants": True,
            "source_rhs_derived": False,
            "boundary_data_derived": False,
            "same_l_split_noether_closed": False,
            "excluded_as_no_axiom_selector": True,
        },
        {
            "family": "curvature_weighted_kinetic",
            "operator_order": 2,
            "free_constants": True,
            "source_rhs_derived": False,
            "boundary_data_derived": False,
            "same_l_split_noether_closed": False,
            "excluded_as_no_axiom_selector": True,
        },
        {
            "family": "scalar_curvature_matching",
            "operator_order": 2,
            "free_constants": True,
            "source_rhs_derived": False,
            "boundary_data_derived": False,
            "same_l_split_noether_closed": False,
            "excluded_as_no_axiom_selector": True,
        },
        {
            "family": "dqtf_dhtf_source_free_kinetic",
            "operator_order": 2,
            "free_constants": True,
            "source_rhs_derived": False,
            "boundary_data_derived": False,
            "same_l_split_noether_closed": False,
            "excluded_as_no_axiom_selector": True,
        },
        {
            "family": "source_derived_stf_curvature_operator",
            "operator_order": "source-fixed",
            "free_constants": False,
            "source_rhs_derived": "required",
            "boundary_data_derived": "required",
            "same_l_split_noether_closed": "required",
            "excluded_as_no_axiom_selector": False,
        },
    ]
    selector_defect_definition = (
        "has_nontrivial_kernel OR free_boundary_constants OR missing_source_rhs "
        "OR missing_source_coefficients OR missing_same_l_split_noether"
    )
    return {
        "description": (
            "Route D nullspace gate: derivative/curvature actions that only produce "
            "homogeneous PDEs are not zero-axiom selectors, because their kernel, "
            "boundary data, coefficients, or same-L Noether split must be chosen."
        ),
        "status": "derivative-curvature-nullspace-gate-open",
        "selector_defect_definition": selector_defect_definition,
        "family_rows": family_rows,
        "homogeneous_source_free_subfamily_excluded": True,
        "source_free_pde_nullspace_probe_status": pde_probe["status"],
        "source_free_boundary_no_go_status": no_go["status"],
        "source_free_boundary_no_go_bounded_claim_closed": bool(no_go["proved_for_source_free_boundary_free_local_pde"]),
        "source_free_pde_excluded_as_no_axiom_selector": bool(
            pde_probe["source_free_pde_excluded_as_no_axiom_selector"]
        ),
        "periodic_kernel_detected": bool(pde_probe["periodic_kernel_detected"]),
        "dirichlet_invertible_but_boundary_unsourced": bool(
            pde_probe["dirichlet_invertible_but_boundary_unsourced"]
        ),
        "derivative_curvature_family_fully_excluded": False,
        "principal_symbol_stability_sufficient": False,
        "source_derived_stf_curvature_operator_open": True,
        "excluded_family_count": sum(1 for row in family_rows if row["excluded_as_no_axiom_selector"]),
        "open_family_count": sum(1 for row in family_rows if not row["excluded_as_no_axiom_selector"]),
        "full_no_go_proved": False,
        "accepted_candidate_exists": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This tightens Route D without overclaiming: source-free derivative and "
            "curvature PDEs are excluded as no-axiom selectors because their nullspace "
            "or boundary/coefficient choices hide a new axiom. A genuinely "
            "source-derived STF curvature operator remains open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D Derivative/Curvature Nullspace Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Selector defect: `{payload['selector_defect_definition']}`",
        f"Source-free PDE nullspace probe status: {payload['source_free_pde_nullspace_probe_status']}",
        f"Source-free/boundary-free no-go status: {payload['source_free_boundary_no_go_status']}",
        f"Source-free/boundary-free bounded claim closed: {payload['source_free_boundary_no_go_bounded_claim_closed']}",
        f"Source-free PDE excluded as no-axiom selector: {payload['source_free_pde_excluded_as_no_axiom_selector']}",
        f"Periodic kernel detected: {payload['periodic_kernel_detected']}",
        f"Dirichlet invertible but boundary unsourced: {payload['dirichlet_invertible_but_boundary_unsourced']}",
        f"Homogeneous source-free subfamily excluded: {payload['homogeneous_source_free_subfamily_excluded']}",
        f"Derivative/curvature family fully excluded: {payload['derivative_curvature_family_fully_excluded']}",
        f"Principal-symbol stability sufficient: {payload['principal_symbol_stability_sufficient']}",
        f"Source-derived STF curvature operator open: {payload['source_derived_stf_curvature_operator_open']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| family | order | free constants | source RHS | boundary data | same-L Noether | excluded |",
        "|---|---:|---:|---|---|---|---:|",
    ]
    for row in payload["family_rows"]:
        lines.append(
            f"| {row['family']} | {row['operator_order']} | {row['free_constants']} | "
            f"{row['source_rhs_derived']} | {row['boundary_data_derived']} | "
            f"{row['same_l_split_noether_closed']} | {row['excluded_as_no_axiom_selector']} |"
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
