from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MHR2, MPL2, VEV, expr_text
    from scripts.derive_svt_curved_branch_desitter_seed import H, A, K, k_phys2
    from scripts.derive_svt_scalar_exact_hr_source_reduction import (
        B_M,
        B_P,
        DPSI_M,
        DPSI_P,
        PHI_M,
        PHI_P,
        PSI_M,
        PSI_P,
        ZETA,
        exact_hr_sources,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MHR2, MPL2, VEV, expr_text
    from derive_svt_curved_branch_desitter_seed import H, A, K, k_phys2
    from derive_svt_scalar_exact_hr_source_reduction import (
        B_M,
        B_P,
        DPSI_M,
        DPSI_P,
        PHI_M,
        PHI_P,
        PSI_M,
        PSI_P,
        ZETA,
        exact_hr_sources,
    )


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_constraints.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_constraints.json"

DZETA = sp.Symbol("dzeta")


def lapse_plus_desitter_constraint() -> sp.Expr:
    return sp.factor(
        MPL2 * (2 * k_phys2() * PSI_P - 6 * H * DPSI_P)
        - exact_hr_sources()["dS_d_phi_p"]
    )


def lapse_minus_desitter_constraint() -> sp.Expr:
    return sp.factor(
        MPL2
        * VEV
        * (2 * k_phys2() * PSI_M / VEV**2 - 6 * H * DPSI_M / VEV)
        - exact_hr_sources()["dS_d_phi_m"]
    )


def shift_plus_desitter_constraint() -> sp.Expr:
    return sp.factor(
        MPL2
        * (
            2 * k_phys2() * (DPSI_P - k_phys2() * B_P)
            - 4 * H * k_phys2() * B_P
        )
        - exact_hr_sources()["dS_d_B_p"]
    )


def shift_minus_desitter_constraint() -> sp.Expr:
    return sp.factor(
        MPL2
        * VEV
        * (
            2 * k_phys2() * (DPSI_M - k_phys2() * B_M) / VEV**2
            - 4 * H * k_phys2() * B_M / VEV
        )
        - exact_hr_sources()["dS_d_B_m"]
    )


def bending_desitter_constraint() -> sp.Expr:
    return sp.factor(
        -2 * MHR2 * MPL2 * (3 * VEV - 3) * k_phys2() * ZETA + 3 * H * DZETA
    )


def rigid_substitutions() -> dict[sp.Symbol, sp.Expr]:
    return {
        PSI_M: -PSI_P / VEV,
        DPSI_M: -DPSI_P / VEV,
    }


def solve_lapse_difference_after_rigidity() -> dict[str, sp.Expr]:
    equations = [
        lapse_plus_desitter_constraint().subs(rigid_substitutions()),
        lapse_minus_desitter_constraint().subs(rigid_substitutions()),
    ]
    solutions = sp.solve(equations, [PHI_P, PHI_M], dict=True, simplify=True)
    if not solutions:
        return {"status": sp.Symbol("no_joint_solution")}
    return {key.name: sp.factor(value) for key, value in solutions[0].items()}


def lapse_compatibility_after_rigidity() -> sp.Expr:
    plus_solution = sp.solve(
        lapse_plus_desitter_constraint().subs(rigid_substitutions()), PHI_P, dict=True
    )[0][PHI_P]
    return sp.factor(
        lapse_minus_desitter_constraint()
        .subs(rigid_substitutions())
        .subs(PHI_P, plus_solution)
    )


def solve_shifts_after_rigidity() -> dict[str, sp.Expr]:
    equations = [
        shift_plus_desitter_constraint().subs(rigid_substitutions()),
        shift_minus_desitter_constraint().subs(rigid_substitutions()),
    ]
    solutions = sp.solve(equations, [B_P, B_M], dict=True, simplify=True)
    return {key.name: sp.factor(value) for key, value in solutions[0].items()}


def solve_bending_mode() -> dict[str, sp.Expr]:
    equation = bending_desitter_constraint()
    if sp.simplify(equation.subs({VEV: 1})) == 3 * H * DZETA:
        return {"v1_solution": sp.Integer(0)}
    solution = sp.solve(equation, DZETA, dict=True, simplify=True)[0][DZETA]
    return {"dzeta": sp.factor(solution)}


def build_payload() -> dict:
    shifts = solve_shifts_after_rigidity()
    lapse_joint = solve_lapse_difference_after_rigidity()
    compatibility = lapse_compatibility_after_rigidity()
    return {
        "artifact": "svt_curved_branch_constraints",
        "status": "curved_constraints_encoded_multipliers_partially_solved",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "constraints": {
            "lapse_plus": expr_text(lapse_plus_desitter_constraint()),
            "lapse_minus": expr_text(lapse_minus_desitter_constraint()),
            "shift_plus": expr_text(shift_plus_desitter_constraint()),
            "shift_minus": expr_text(shift_minus_desitter_constraint()),
            "bending": expr_text(bending_desitter_constraint()),
        },
        "rigidity": {
            "psi_minus": "-psi_plus/v",
            "dpsi_minus": "-dpsi_plus/v",
        },
        "solutions": {
            "lapse_joint": {key: expr_text(value) for key, value in lapse_joint.items()},
            "lapse_compatibility_after_plus": expr_text(compatibility),
            "lapse_compatibility_v1": expr_text(compatibility.subs(VEV, 1)),
            "B_p": expr_text(shifts["B_p"]),
            "B_m": expr_text(shifts["B_m"]),
            "bending": {key: expr_text(value) for key, value in solve_bending_mode().items()},
        },
        "closed_primitives": [
            "plus/minus dS lapse constraints encoded",
            "plus/minus dS shift constraints encoded",
            "dS bending friction equation encoded",
            "shift multipliers solved after rigidity",
            "lapse compatibility vanishes on the v=1 curved witness branch",
        ],
        "still_open_primitives": [
            "joint lapse system still has compatibility requirements unless full dS source terms cancel them",
            "full dS scalar action with radion/Aether is not reinjected",
            "no dS kinetic/gradient matrix has been derived yet",
        ],
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Constraints",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Solutions",
    ]
    for key, value in payload["solutions"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Still Open"])
    lines.extend(f"- {item}" for item in payload["still_open_primitives"])
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
