from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_radion_background_dynamics.md")
JSON_PATH = Path("outputs/reports/p0_eft_radion_background_dynamics.json")


def build_payload() -> dict:
    equation = {
        "variable": "x=ln(a)",
        "kg_time_form": "chi_ddot + 3H chi_dot + dV/dchi = Source_spinor_boundary",
        "kg_x_form": "chi_xx + (3 + H_x/H)chi_x + (1/H^2)dV/dchi = Source/H^2",
        "torsion_density": "Omega_T(a)=chi_dot^2/(3 M_pl^2 H^2)=chi_x^2/(3 M_pl^2)",
    }
    dynamics = {
        "early": "Hubble friction can freeze chi_x -> 0",
        "transition": "boundary/source kick can excite chi_x near a_Sigma",
        "late": "relaxation depends on V(chi) around the selected dS vacuum",
    }
    theorem_status = {
        "radion_KG_structure_encoded": True,
        "Omega_T_extraction_encoded": True,
        "potential_V_fixed_from_Janus_action": False,
        "spinor_boundary_source_fixed": False,
        "radion_background_solution_ready": False,
        "Omega_T_no_fit_ready": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive V(chi) from the Janus/Cartan action used in the boundary sector",
        "derive Source_spinor_boundary from RUN 1 boundary terms",
        "then integrate chi(x) and export Omega_T(a) into the growth solver",
    ]
    return {
        "description": "Radion background dynamics target for no-fit Omega_torsion_unit(a).",
        "status": "radion-KG-structured-potential-source-open",
        "equation": equation,
        "dynamics": dynamics,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The no-fit route to Omega_T(a) is the radion KG background. The equation is "
            "structured, but V(chi) and the boundary spinor source must be derived from the "
            "same Janus action before numerical integration is predictive."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Radion Background Dynamics",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Equation",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["equation"].items())
    lines.extend(["", "## Dynamics"])
    lines.extend(f"- {key}: {value}" for key, value in payload["dynamics"].items())
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
