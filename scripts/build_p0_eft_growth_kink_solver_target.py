from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_growth_kink_solver_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_growth_kink_solver_target.json")


def build_payload() -> dict:
    growth_system = {
        "state": "X=[delta_m, ddelta_m/dln a]",
        "bulk_equation": "delta'' + (2+H'/H)delta' - (3/2)Omega_m(a) mu(k,a) delta = 0",
        "jump_condition": "delta_+=delta_-; delta'_+=delta'_- + S_kink(k,a_Sigma)",
        "non_singularity": "matter density contrast remains continuous; growth velocity jumps",
    }
    geff = {
        "mu_definition": "mu(k,a)=G_eff(k,a)/G_N",
        "safe_status": "target-to-derive from transported active stress",
        "yukawa_like_candidate": "1 + alpha_J*k^2/(k^2+M_eff^2(a))",
        "mass_gap": "M_eff^2 linked to dS/Lichnerowicz scale conditionally",
    }
    theorem_status = {
        "growth_state_defined": True,
        "kink_jump_condition_encoded": True,
        "delta_continuity_encoded": True,
        "geff_ansatz_marked_unproved": True,
        "growth_solver_implemented": False,
        "fsigma8_prediction_ready": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive mu(k,a) from active transported stress, not fit it",
        "derive S_kink from Delta(partial_n(Psi-Phi)) and matter Euler projection",
        "implement numerical integration for f_sigma8 once mu and S_kink are fixed",
    ]
    return {
        "description": "Kink-only linear growth solver target for f_sigma8.",
        "status": "growth-kink-target-open",
        "growth_system": growth_system,
        "geff": geff,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The growth problem is now a jump ODE: delta is continuous, delta' receives S_kink. "
            "The solver waits on derived mu(k,a) and S_kink."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Growth Kink Solver Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Growth System",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["growth_system"].items())
    lines.extend(["", "## G_eff"])
    lines.extend(f"- {key}: {value}" for key, value in payload["geff"].items())
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
