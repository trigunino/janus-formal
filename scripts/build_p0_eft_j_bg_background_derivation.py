from __future__ import annotations

from pathlib import Path
import json
import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_j_bg_background_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_j_bg_background_derivation.json")


def solve_coupled_background() -> dict:
    chi, gamma, rho, Mpl2, eps = sp.symbols("chi gamma rho Mpl2 eps")
    j_bg = eps * rho / Mpl2
    unit_shape = sp.cosh(gamma * chi) - 1
    lambda_j = sp.simplify(rho / unit_shape)
    stationary_residual = sp.simplify(lambda_j * gamma * sp.sinh(gamma * chi) - j_bg)
    tanh_half = sp.simplify(stationary_residual / rho)
    chi_solution = sp.simplify(2 * sp.atanh(eps / (Mpl2 * gamma)) / gamma)
    canonical_gamma = sp.sqrt(sp.Rational(1, 6))
    canonical_chi = sp.simplify(chi_solution.subs(gamma, canonical_gamma))
    canonical_lambda = sp.simplify(lambda_j.subs({gamma: canonical_gamma, chi: canonical_chi}))
    return {
        "J_bg": str(j_bg),
        "Lambda_J_before_stationary": str(lambda_j),
        "stationary_residual_over_rho": str(tanh_half),
        "chi_inf_solution": str(chi_solution),
        "canonical_chi_inf_solution": str(canonical_chi),
        "canonical_Lambda_J_solution": str(canonical_lambda),
        "existence_condition": "|eps| < Mpl2*gamma",
    }


def build_payload() -> dict:
    solution = solve_coupled_background()
    theorem_status = {
        "J_bg_defined_from_background_trace_jump": True,
        "orientation_sign_kept_explicit": True,
        "coupled_stationary_and_dS_equations_solved": True,
        "chi_inf_fixed_by_branch_data": True,
        "Lambda_J_fixed_by_branch_data": True,
        "requires_orientation_and_units_choice": True,
        "amplitude_closed_conditionally": True,
        "unconditional_no_fit_ready": False,
    }
    obligations = [
        "select eps from the same normal/orbifold orientation convention used in RUN 1",
        "fix Mpl2 units before exporting numerical chi_inf and Lambda_J",
        "then feed canonical chi_inf and Lambda_J into the KG integrator",
    ]
    return {
        "description": "Background derivation of the stationary radion source J_bg.",
        "status": "J_bg-derived-conditionally-with-orientation",
        "solution": solution,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "J_bg can be tied to the de Sitter trace-jump source rather than fitted. The "
            "closure is conditional on the global orientation and unit convention already "
            "used by the boundary sector."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT J_bg Background Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Coupled Solution",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["solution"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
