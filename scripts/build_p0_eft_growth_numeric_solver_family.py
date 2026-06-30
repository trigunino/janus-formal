from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_growth_numeric_solver_family.md")
JSON_PATH = Path("outputs/reports/p0_eft_growth_numeric_solver_family.json")


def build_payload() -> dict:
    omega_torsion = {
        "profile_family": "Omega_T(a)=Omega_T0*a^s/(1+(a/a_Sigma)^r)",
        "purpose": "symbolic no-fit family until Janus radion background is derived",
        "bbn_cmb_safety_condition": "Omega_T(a<<a_Sigma) small",
        "status": "parametric-family-not-final-background",
    }
    solver = {
        "variable": "x=ln(a)",
        "state": "X=[delta, ddelta/dx]",
        "ode": "delta_xx + (2+dlnH/dx)delta_x - (3/2)Omega_m(a)*mu(k,a)*delta = 0",
        "kick": "X2_+ = X2_- + S_kink(k,a_Sigma)",
        "integration": "piecewise before/after x_Sigma",
    }
    theorem_status = {
        "numeric_solver_family_specified": True,
        "piecewise_kick_integration_specified": True,
        "Omega_torsion_background_derived_from_Janus": False,
        "S_kink_amplitude_derived": False,
        "fsigma8_family_ready": True,
        "fsigma8_prediction_no_fit_ready": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive Omega_T(a) from radion/background Janus equations",
        "derive S_kink amplitude from Euler projection",
        "then run numeric solve_ivp with fixed derived functions",
    ]
    return {
        "description": "Executable-family specification for EC-branch growth ODE with kink.",
        "status": "fsigma8-family-ready-not-final-prediction",
        "omega_torsion": omega_torsion,
        "solver": solver,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The growth integrator can be implemented as a parametric family now. A final no-fit "
            "f_sigma8 prediction still requires Janus-derived Omega_T(a) and S_kink."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Growth Numeric Solver Family",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Omega Torsion",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["omega_torsion"].items())
    lines.extend(["", "## Solver"])
    lines.extend(f"- {key}: {value}" for key, value in payload["solver"].items())
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
