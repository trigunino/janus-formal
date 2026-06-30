from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_flrw_zero_divergence_toy_solution.md")
JSON_PATH = Path("outputs/reports/p0_flrw_zero_divergence_toy_solution.json")


def build_payload() -> dict:
    assumptions = [
        "homogeneous FLRW",
        "common cosmic time for the toy branch",
        "dust only: p_plus=p_minus=0 and Pi=0",
        "comoving aligned tetrads: L_minus_to_plus=I",
        "same-sector dust conservation: dot(rho_s)+3 H_s rho_s=0",
    ]
    plus_solution = {
        "pde": "dot(B_plus k_plus rho_minus)+3 H_plus B_plus k_plus rho_minus=0",
        "using_minus_conservation": "dot(rho_minus)=-3 H_minus rho_minus",
        "solution_condition": "d_t log(B_plus k_plus)=3(H_minus-H_plus)",
        "combined_weight": "B_plus k_plus proportional (a_minus/a_plus)^3",
        "interpretation": "k_plus is the scalar transport factor left after the determinant layer B_plus",
    }
    minus_solution = {
        "pde": "dot(B_minus k_minus rho_plus)+3 H_minus B_minus k_minus rho_plus=0",
        "using_plus_conservation": "dot(rho_plus)=-3 H_plus rho_plus",
        "solution_condition": "d_t log(B_minus k_minus)=3(H_plus-H_minus)",
        "combined_weight": "B_minus k_minus proportional (a_plus/a_minus)^3",
        "interpretation": "k_minus is the scalar transport factor left after the determinant layer B_minus",
    }
    determinant_split = [
        "if B_plus=(a_minus/a_plus)^n then k_plus proportional (a_minus/a_plus)^(3-n)",
        "if B_minus=(a_plus/a_minus)^n then k_minus proportional (a_plus/a_minus)^(3-n)",
        "n=4 gives k proportional inverse scale-ratio, but combined B*k remains cubic",
        "B is not an optical Q_cross amplitude",
    ]
    closed = [
        "zero-divergence PDE algebra closes in homogeneous dust scalar branch",
        "D log B terms are not dropped; they are balanced by k transport",
        "branch agrees with earlier FLRW dust transport audit",
    ]
    not_closed = [
        "non-comoving perturbations",
        "nontrivial L/F_alpha",
        "pressure/projector/Pi transport",
        "unique generic K tensor",
        "Q_cross lensing normalization",
    ]
    return {
        "description": "Toy FLRW dust solution of the M30 zero-divergence PDE.",
        "status": "toy-branch-closed",
        "toy_branch_closed": True,
        "generic_physics_closed": False,
        "prediction_ready": False,
        "assumptions": assumptions,
        "plus_solution": plus_solution,
        "minus_solution": minus_solution,
        "determinant_split": determinant_split,
        "closed": closed,
        "not_closed": not_closed,
        "verdict": (
            "The source-derived PDE reproduces the cubic FLRW dust transport law. "
            "This validates the algebraic route but does not solve the generic "
            "non-comoving tensor problem."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 FLRW Zero-Divergence Toy Solution",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Toy branch closed: {payload['toy_branch_closed']}",
        f"Generic physics closed: {payload['generic_physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Assumptions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["assumptions"])
    for title, key in (("Plus Solution", "plus_solution"), ("Minus Solution", "minus_solution")):
        lines.extend(["", f"## {title}", ""])
        for name, value in payload[key].items():
            lines.append(f"- {name}: `{value}`")
    lines.extend(["", "## Determinant Split", ""])
    lines.extend(f"- {item}" for item in payload["determinant_split"])
    lines.extend(["", "## Closed", ""])
    lines.extend(f"- {item}" for item in payload["closed"])
    lines.extend(["", "## Not Closed", ""])
    lines.extend(f"- {item}" for item in payload["not_closed"])
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
