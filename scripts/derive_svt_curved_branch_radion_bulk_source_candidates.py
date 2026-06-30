from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_boundary_derivative_invariant_search import (
        gradient_decomposition,
    )
    from scripts.derive_svt_curved_branch_desitter_seed import A, H, K
    from scripts.derive_svt_quadratic_coefficients import MPL2, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_boundary_derivative_invariant_search import (
        gradient_decomposition,
    )
    from derive_svt_curved_branch_desitter_seed import A, H, K
    from derive_svt_quadratic_coefficients import MPL2, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_radion_bulk_source_candidates.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_radion_bulk_source_candidates.json"


XI, ETA, BND = sp.symbols("xi eta bnd")


def target_families() -> dict[str, sp.Expr]:
    return gradient_decomposition()


def xi_chi_R_signature() -> dict[str, sp.Expr]:
    parts = target_families()
    return {
        "no_spatial_gradient": parts["no_spatial_gradient"],
        "D_K_D_K_like": sp.Integer(0),
        "Delta_K_squared_like": sp.Integer(0),
    }


def horndeski_bulk_signature() -> dict[str, sp.Expr]:
    parts = target_families()
    return {
        "no_spatial_gradient": sp.Integer(0),
        "D_K_D_K_like": parts["D_K_D_K_like"],
        "Delta_K_squared_like": sp.Integer(0),
    }


def horndeski_boundary_completion_signature() -> dict[str, sp.Expr]:
    parts = target_families()
    return {
        "no_spatial_gradient": sp.Integer(0),
        "D_K_D_K_like": sp.Integer(0),
        "Delta_K_squared_like": parts["Delta_K_squared_like"],
    }


def combined_candidate(include_boundary_completion: bool) -> dict[str, sp.Expr]:
    xi = xi_chi_R_signature()
    hor = horndeski_bulk_signature()
    bnd = horndeski_boundary_completion_signature()
    return {
        key: sp.factor(XI * xi[key] + ETA * hor[key] + (BND * bnd[key] if include_boundary_completion else 0))
        for key in target_families()
    }


def solve_family_identity(include_boundary_completion: bool) -> list[dict]:
    candidate = combined_candidate(include_boundary_completion)
    equations = [
        sp.factor(candidate[key] - target_families()[key])
        for key in target_families()
    ]
    unknowns = [XI, ETA] + ([BND] if include_boundary_completion else [])
    raw_solutions = sp.solve(equations, unknowns, dict=True)
    return [
        solution
        for solution in raw_solutions
        if all(sp.simplify(equation.subs(solution)) == 0 for equation in equations)
    ]


def build_payload() -> dict:
    bulk_only_solutions = solve_family_identity(include_boundary_completion=False)
    completed_solutions = solve_family_identity(include_boundary_completion=True)
    return {
        "artifact": "svt_curved_branch_radion_bulk_source_candidates",
        "status": "bulk_radion_terms_need_horndeski_boundary_completion_for_k4_block",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "target_families": {key: expr_text(value) for key, value in target_families().items()},
        "xi_chi_R_signature": {key: expr_text(value) for key, value in xi_chi_R_signature().items()},
        "horndeski_bulk_signature": {key: expr_text(value) for key, value in horndeski_bulk_signature().items()},
        "horndeski_boundary_completion_signature": {
            key: expr_text(value) for key, value in horndeski_boundary_completion_signature().items()
        },
        "bulk_only_constant_solutions": [
            {str(key): expr_text(value) for key, value in solution.items()}
            for solution in bulk_only_solutions
        ],
        "with_boundary_completion_constant_solutions": [
            {str(key): expr_text(value) for key, value in solution.items()}
            for solution in completed_solutions
        ],
        "verdict": {
            "xi_chi_R_alone_sufficient": False,
            "horndeski_bulk_alone_sufficient": False,
            "bulk_pair_sufficient": bool(bulk_only_solutions),
            "requires_horndeski_boundary_completion": not bool(bulk_only_solutions),
            "completed_family_can_span_target": bool(completed_solutions),
            "source_derived_from_janus": False,
            "prediction_ready": False,
        },
        "next_inputs": [
            "derive the Horndeski boundary completion from the covariant radion action",
            "then prove its coefficient is fixed by second-order field equations, not chosen by inverse matching",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Radion Bulk Source Candidates",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Verdict",
    ]
    for key, value in payload["verdict"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Next Inputs"])
    lines.extend(f"- {item}" for item in payload["next_inputs"])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
