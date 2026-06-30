from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_growth_kink_mu_functions.md")
JSON_PATH = Path("outputs/reports/p0_eft_growth_kink_mu_functions.json")


def build_payload() -> dict:
    skink = {
        "formula_target": "S_kink(k,aS)=-(k^2/(H^2*aS^2))*Delta(partial_n(Psi-Phi))",
        "source": "Euler projection of derivative-slip jump",
        "status": "encoded as projection target",
        "coefficient_exact": False,
    }
    mu = {
        "formula": "mu(k,a)=1+alpha_Janus(a)*k^2/(k^2+M_eff^2(a))",
        "M_eff2": "3*H(a)^2/2 conditionally from Lichnerowicz/dS boundary gap",
        "alpha_Janus": "must be derived from transported active stress and Pi",
        "status": "M_eff closed conditionally; alpha open",
    }
    solver = {
        "bulk_ode": "delta''+(2+H'/H)delta'-(3/2)Omega_m(a)*mu(k,a)*delta=0",
        "jump": "delta continuous; delta' receives S_kink",
        "fsigma8": "f_sigma8 requires integrating this ODE after alpha_Janus and S_kink coefficient close",
    }
    theorem_status = {
        "skink_formula_encoded": True,
        "skink_coefficient_derived": False,
        "mu_form_encoded": True,
        "M_eff2_conditionally_closed": True,
        "alpha_Janus_derived": False,
        "growth_solver_ready_to_implement": False,
        "fsigma8_prediction_ready": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive exact Euler projection coefficient for S_kink",
        "derive alpha_Janus(a) from transported active stress including Pi",
        "then implement ODE integration for f_sigma8",
    ]
    return {
        "description": "Kink source and mu(k,a) functions for the Janus growth solver.",
        "status": "growth-functions-partial-alpha-open",
        "skink": skink,
        "mu": mu,
        "solver": solver,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "M_eff is conditionally fixed by the dS/Lichnerowicz gap and the kink source form "
            "is encoded. The final non-fit macro coefficient is alpha_Janus(a), which must come "
            "from transported active stress and anisotropic moments."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Growth Kink Mu Functions",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## S_kink",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["skink"].items())
    lines.extend(["", "## mu(k,a)"])
    lines.extend(f"- {key}: {value}" for key, value in payload["mu"].items())
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
