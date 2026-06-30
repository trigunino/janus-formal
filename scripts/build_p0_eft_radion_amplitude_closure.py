from __future__ import annotations

from pathlib import Path
import json
import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_radion_amplitude_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_radion_amplitude_closure.json")


def solve_lambda_j() -> dict:
    chi_inf, gamma, rho_dS = sp.symbols("chi_inf gamma rho_dS")
    unit_shape = sp.cosh(gamma * chi_inf) - 1
    lambda_j = sp.simplify(rho_dS / unit_shape)
    canonical = lambda_j.subs(gamma, sp.sqrt(sp.Rational(1, 6)))
    return {
        "background_equation": "Lambda_J*(cosh(gamma*chi_inf)-1)=rho_dS_residual",
        "unit_shape": str(unit_shape),
        "Lambda_J_solution": str(lambda_j),
        "canonical_Lambda_J_solution": str(canonical),
        "nondegenerate_condition": "chi_inf != 0 and rho_dS_residual != 0",
        "degenerate_origin": "if chi_inf=0 then V(0)=0, so Lambda_J cannot source dS by itself",
    }


def build_payload() -> dict:
    closure = solve_lambda_j()
    theorem_status = {
        "background_equation_encoded": True,
        "Lambda_J_solved_algebraically": True,
        "requires_nonzero_asymptotic_radion": True,
        "chi_inf_fixed_by_Janus_background": False,
        "rho_dS_residual_fixed": False,
        "potential_fully_fixed_no_fit": False,
    }
    obligations = [
        "fix rho_dS_residual from the selected dS branch convention",
        "derive chi_inf from the Janus background/holonomy condition",
        "then substitute Lambda_J into the KG solver",
    ]
    return {
        "description": "Algebraic closure of the Janus radion potential amplitude.",
        "status": "Lambda_J-reduced-to-background-data",
        "closure": closure,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "Lambda_J is no longer an independent fit parameter once rho_dS_residual and "
            "chi_inf are supplied by the background branch. The branch chi_inf=0 cannot "
            "generate de Sitter energy from this normalized cosh potential."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Radion Amplitude Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Closure",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["closure"].items())
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
