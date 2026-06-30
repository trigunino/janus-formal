from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_desitter_seed import A, H, K
    from scripts.derive_svt_curved_branch_constraints import solve_shifts_after_rigidity
    from scripts.derive_svt_quadratic_coefficients import LAMBDA_PHI, MHR2, MPL2, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_desitter_seed import A, H, K
    from derive_svt_curved_branch_constraints import solve_shifts_after_rigidity
    from derive_svt_quadratic_coefficients import LAMBDA_PHI, MHR2, MPL2, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_effective_mode.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_effective_mode.json"

PSI, DPSI, CHI, DCHI, A0 = sp.symbols("psi dpsi chi dchi A0")


def k_phys2() -> sp.Expr:
    return K**2 / A**2


def eh_ds_density(b_p: sp.Expr) -> sp.Expr:
    return MPL2 * (
        -6 * DPSI**2
        + 18 * H**2 * PSI**2
        - 2 * k_phys2() * PSI**2
        + 4 * k_phys2() * DPSI * b_p
    )


def radion_ds_density() -> sp.Expr:
    return (
        sp.Rational(1, 2) * DCHI**2
        - sp.Rational(1, 2) * k_phys2() * CHI**2
        - 4 * LAMBDA_PHI * CHI**2
        + 3 * MPL2 * DPSI * DCHI
    )


def aether_ds_density() -> sp.Expr:
    return (
        -sp.Rational(1, 2) * k_phys2() * A0**2
        - 2 * MPL2 * (K / A) * A0 * (DPSI + DCHI)
    )


def shift_plus_v1() -> sp.Expr:
    shifts = solve_shifts_after_rigidity()
    return sp.factor(shifts["B_p"].subs({sp.Symbol("v"): 1, sp.Symbol("dpsi_p"): DPSI}))


def total_density_before_aether_elimination() -> sp.Expr:
    return sp.factor(eh_ds_density(shift_plus_v1()) + radion_ds_density() + aether_ds_density())


def eliminate_aether(density: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    solution = sp.solve(sp.diff(density, A0), A0, dict=True)[0][A0]
    return sp.factor(solution), sp.factor(density.subs(A0, solution))


def boundary_substitution() -> dict[sp.Symbol, sp.Expr]:
    return {
        CHI: 2 * MPL2 * PSI,
        DCHI: 2 * MPL2 * DPSI,
    }


def effective_density() -> sp.Expr:
    _, no_aether = eliminate_aether(total_density_before_aether_elimination())
    return sp.factor(sp.cancel(no_aether.subs(boundary_substitution())))


def kernels() -> dict[str, sp.Expr]:
    density = effective_density()
    alpha = sp.factor(sp.diff(density, DPSI, 2) / 2)
    psi_kernel = sp.factor(sp.diff(density, PSI, 2) / 2)
    beta = sp.factor(-psi_kernel / k_phys2())
    return {
        "alpha_dS": alpha,
        "psi2_kernel": psi_kernel,
        "beta_dS": beta,
        "cs2": sp.factor(beta / alpha),
    }


def witness_subs() -> dict[sp.Symbol, sp.Expr]:
    return {
        MPL2: 4,
        MHR2: 1,
        LAMBDA_PHI: 1,
        H**2: sp.Rational(1, 2),
    }


def witness_kernels() -> dict[str, sp.Expr]:
    return {
        key: sp.factor(value.subs(witness_subs()))
        for key, value in kernels().items()
    }


def sample_domain_values() -> list[dict]:
    values = []
    base = {
        MPL2: 4,
        MHR2: 1,
        LAMBDA_PHI: 1,
        H: sp.sqrt(sp.Rational(1, 2)),
        A: 1,
    }
    for kval in [sp.Rational(1, 2), 1, 2]:
        sample = {**base, K: kval}
        evaluated = {key: sp.N(value.subs(sample)) for key, value in kernels().items()}
        values.append(
            {
                "k": str(kval),
                "alpha_dS": str(evaluated["alpha_dS"]),
                "beta_dS": str(evaluated["beta_dS"]),
                "cs2": str(evaluated["cs2"]),
                "alpha_positive": bool(evaluated["alpha_dS"] > 0),
                "beta_positive": bool(evaluated["beta_dS"] > 0),
                "cs2_nonnegative": bool(evaluated["cs2"] >= 0),
            }
        )
    return values


def build_payload() -> dict:
    a0_solution, _ = eliminate_aether(total_density_before_aether_elimination())
    exact = kernels()
    witness = witness_kernels()
    return {
        "artifact": "svt_curved_branch_effective_mode",
        "status": "curved_branch_unique_mode_reduced_under_supplied_blocks",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "assumptions": {
            "v": 1,
            "phi_plus": 0,
            "zeta": 0,
            "boundary_constraint": "chi = 2*Mpl2*psi",
            "aether_eliminated": True,
            "H2_witness": "1/2",
        },
        "shift_plus_v1": expr_text(shift_plus_v1()),
        "aether_solution": expr_text(a0_solution),
        "effective_density": expr_text(effective_density()),
        "kernels": {key: expr_text(value) for key, value in exact.items()},
        "witness_kernels": {key: expr_text(value) for key, value in witness.items()},
        "witness_signs": {
            "alpha_positive_symbolic_condition": "inspect witness alpha over a,k,H sign domain",
            "beta_positive_symbolic_condition": "inspect witness beta over a,k,H sign domain",
            "no_numeric_k_a_sample_claimed": True,
        },
        "sample_domain_H_sqrt_half_a1": sample_domain_values(),
        "prediction_ready": False,
        "still_open_primitives": [
            "prove alpha_dS and beta_dS positivity over the physical k/a domain",
            "fix time-dependent H sign convention rather than substituting only H^2",
            "derive supplied dS action blocks from full Cartan expansion",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Effective Mode",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Witness Kernels",
    ]
    for key, value in payload["witness_kernels"].items():
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
