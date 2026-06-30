from __future__ import annotations

from pathlib import Path
import json
import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_chi_infinity_stationary_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_chi_infinity_stationary_closure.json")


def stationary_solution() -> dict:
    chi, gamma, Lambda_J, J_bg = sp.symbols("chi gamma Lambda_J J_bg")
    dV = Lambda_J * gamma * sp.sinh(gamma * chi)
    eq = sp.Eq(dV, J_bg)
    chi_solution = sp.asinh(J_bg / (Lambda_J * gamma)) / gamma
    canonical = sp.simplify(chi_solution.subs(gamma, sp.sqrt(sp.Rational(1, 6))))
    return {
        "stationary_equation": "Lambda_J*gamma*sinh(gamma*chi_inf)=J_bg",
        "cosh_alone_solution": "chi_inf=0 when J_bg=0",
        "nonzero_solution": str(chi_solution),
        "canonical_nonzero_solution": str(canonical),
        "required_background_force": "J_bg != 0",
    }


def build_payload() -> dict:
    solution = stationary_solution()
    theorem_status = {
        "cosh_potential_derivative_computed": True,
        "cosh_alone_forces_chi_inf_zero": True,
        "nonzero_chi_inf_requires_background_source": True,
        "stationary_solution_with_J_bg_encoded": True,
        "J_bg_derived_from_Janus_background": False,
        "chi_inf_fixed_by_Janus_background": False,
        "amplitude_fully_closed": False,
    }
    obligations = [
        "derive J_bg from the background Einstein-Palatini junction or residual tension",
        "then substitute chi_inf=asinh(J_bg/(Lambda_J*gamma))/gamma into Lambda_J closure",
        "solve the coupled pair {stationary equation, dS energy equation}",
    ]
    return {
        "description": "Stationary chi_inf closure for the Janus radion potential.",
        "status": "nonzero-chi-inf-requires-background-force",
        "stationary": solution,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "A nonzero chi_inf cannot be obtained from the normalized cosh potential alone. "
            "It requires a background force J_bg from the Janus junction. This is the correct "
            "remaining object to derive, not another free radion parameter."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Chi Infinity Stationary Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Stationary Equation",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["stationary"].items())
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
