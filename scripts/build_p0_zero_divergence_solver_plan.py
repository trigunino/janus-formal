from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_zero_divergence_solver_plan.md")
JSON_PATH = Path("outputs/reports/p0_zero_divergence_solver_plan.json")


def build_payload() -> dict:
    unknowns = [
        "K_plus^{mu nu}",
        "K_minus^{mu nu}",
        "optional L_minus_to_plus when K is parameterized as transported matter",
        "Omega_alpha=(D_alpha L)L^{-1} with eta-antisymmetry",
    ]
    equations = [
        "D_plus_nu(B_4vol_plus_from_minus K_plus^{mu nu}) = -D_plus_nu T_plus^{mu nu}",
        "D_minus_nu(B_4vol_minus_from_plus K_minus^{mu nu}) = -D_minus_nu T_minus^{mu nu}",
        "Omega_{alpha AB}+Omega_{alpha BA}=0",
        "same L induces K_plus/K_minus and Q_cross",
    ]
    solver_branches = [
        {
            "branch": "direct_divergence_pde_for_K",
            "method": "solve K as symmetric tensor field subject to two divergence equations and boundary conditions",
            "advantage": "closest to M30 zero-divergence principle",
            "open_problem": "underdetermined without symmetry, boundary, gauge or constitutive law",
            "prediction_ready": False,
        },
        {
            "branch": "transported_matter_parameterization",
            "method": "set K_plus=L*T_minus*L^T plus matter terms, then solve PDE contractions for Omega/F",
            "advantage": "ties K and Q_cross through same L",
            "open_problem": "PDE sees only divergence contractions; transverse Lorentz gauge remains",
            "prediction_ready": False,
        },
        {
            "branch": "minimal_norm_pde_gauge",
            "method": "choose the lowest-norm K or Omega among PDE solutions",
            "advantage": "numerically well-posed diagnostic candidate",
            "open_problem": "minimal norm is an added principle unless derived from action/symmetry",
            "prediction_ready": False,
        },
    ]
    closure_tests = [
        "substitute solved K_plus into R_plus and verify zero tensorially",
        "substitute solved K_minus into R_minus and verify zero tensorially",
        "verify B_4vol product-rule terms are present in the PDE residual",
        "verify same L gives optical Q_cross if transported branch is used",
        "verify Newtonian/TOV limits match M30 weak-field accepted behavior",
        "verify pressure/projector/Pi terms are explicit for non-dust sources",
    ]
    next_artifacts = [
        "build a toy symbolic 1D/FLRW PDE branch to validate algebra",
        "build a non-comoving dust transported-matter PDE residual",
        "build a uniqueness/gauge audit for direct K PDE solutions",
    ]
    return {
        "description": "Solver plan for the M30 zero-divergence interaction-tensor PDE.",
        "status": "solver-plan-open",
        "source_pde_route": True,
        "unknowns_declared": True,
        "solver_branches_written": True,
        "unique_solution_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "unknowns": unknowns,
        "equations": equations,
        "solver_branches": solver_branches,
        "closure_tests": closure_tests,
        "next_artifacts": next_artifacts,
        "verdict": (
            "The source-derived PDE route is actionable, but not unique. The next "
            "valid progress is to solve controlled branches and audit uniqueness, "
            "not to promote the conditional solution to a prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Zero-Divergence Solver Plan",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source PDE route: {payload['source_pde_route']}",
        f"Unique solution found: {payload['unique_solution_found']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Unknowns",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["unknowns"])
    lines.extend(["", "## Equations", ""])
    lines.extend(f"- `{item}`" for item in payload["equations"])
    lines.extend(["", "## Solver Branches", ""])
    for row in payload["solver_branches"]:
        lines.append(f"- {row['branch']}: {row['method']}")
        lines.append(f"  - advantage: {row['advantage']}")
        lines.append(f"  - open problem: {row['open_problem']}")
        lines.append(f"  - prediction ready: {row['prediction_ready']}")
    lines.extend(["", "## Closure Tests", ""])
    lines.extend(f"- {item}" for item in payload["closure_tests"])
    lines.extend(["", "## Next Artifacts", ""])
    lines.extend(f"- {item}" for item in payload["next_artifacts"])
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
