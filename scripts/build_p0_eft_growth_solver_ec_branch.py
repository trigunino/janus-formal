from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_growth_solver_ec_branch.md")
JSON_PATH = Path("outputs/reports/p0_eft_growth_solver_ec_branch.json")


def build_payload() -> dict:
    mu = {
        "branch": "standard EC no-Holst isotropic spinless",
        "alpha_iso": "161/36 * Omega_torsion_unit(a)",
        "mu": "1 + (161/36)*Omega_torsion_unit(a)*k^2/(k^2 + 3*H(a)^2/2)",
        "ir_limit": "mu -> 1 as k/H -> 0",
        "uv_limit": "mu -> 1 + (161/36)*Omega_torsion_unit(a) as k/H -> infinity",
    }
    solver = {
        "ode": "delta''+(2+H'/H)delta'-(3/2)Omega_m(a)*mu(k,a)*delta=0",
        "jump": "delta continuous; delta' receives S_kink at a=a_Sigma",
        "f_sigma8": "f=dln(delta)/dlna; f_sigma8=f*sigma8_norm*delta/delta_today",
        "ready_to_integrate": "requires Omega_torsion_unit(a), H(a), Omega_m(a), a_Sigma, and S_kink",
    }
    theorem_status = {
        "mu_iso_EC_branch_closed": True,
        "growth_solver_equations_closed_symbolically": True,
        "Omega_torsion_unit_background_specified": False,
        "S_kink_numeric_or_symbolic_closed": False,
        "growth_solver_isotropic_ready": False,
        "fsigma8_curve_generated": False,
        "full_cosmology_prediction_ready": False,
    }
    obligations = [
        "specify Omega_torsion_unit(a) from the background branch",
        "close S_kink coefficient or run kink-only symbolic family",
        "then integrate the ODE for f_sigma8(z)",
    ]
    return {
        "description": "Growth solver equations for the standard EC isotropic branch.",
        "status": "mu-closed-growth-background-inputs-open",
        "mu": mu,
        "solver": solver,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "mu(k,a) is closed for the standard EC isotropic branch. The ODE is ready in form, "
            "but numerical/symbolic f_sigma8 still needs the background Omega_torsion_unit(a) "
            "and S_kink closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Growth Solver EC Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## mu(k,a)",
    ]
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
