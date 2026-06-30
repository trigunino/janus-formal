from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_spinless_isotropic_alpha_branch.md")
JSON_PATH = Path("outputs/reports/p0_eft_spinless_isotropic_alpha_branch.json")


def build_payload() -> dict:
    assumptions = {
        "matter": "spinless Vlasov",
        "distribution": "isotropic in receiver tetrad momentum frame",
        "anisotropic_stress": "Pi=0 conditionally",
        "validity": "baseline branch only; not general Vlasov closure",
    }
    alpha = {
        "contorsion_baseline": "alpha_Janus_iso(a) proportional to (q_T^2+q_A^2)*Omega_torsion(a)",
        "Omega_torsion": "rho_torsion_eff(a)/rho_crit(a)",
        "with_pin_values": "q_T=1, q_A^2=1/6 gives q_T^2+q_A^2=7/6",
        "result": "alpha_Janus_iso(a) = (7/6)*Omega_torsion(a) up to normalization of T_eff_torsion",
    }
    theorem_status = {
        "isotropic_spinless_branch_defined": True,
        "pi_zero_conditionally": True,
        "contorsion_combination_computed": True,
        "alpha_iso_formula_encoded": True,
        "torsion_energy_normalization_derived": False,
        "alpha_iso_fully_derived": False,
        "general_anisotropic_branch_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive normalization of rho_torsion_eff from the contorsion stress tensor",
        "keep general Pi branch open for non-isotropic distributions",
        "use alpha_iso only for baseline/no-fit exploratory growth runs",
    ]
    return {
        "description": "Spinless isotropic baseline branch for alpha_Janus(a).",
        "status": "alpha-iso-branch-partial-normalization-open",
        "assumptions": assumptions,
        "alpha": alpha,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The isotropic spinless branch gives a clean alpha structure with Pi=0 conditionally. "
            "It still needs the normalization of rho_torsion_eff before f_sigma8 can be predicted."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Spinless Isotropic Alpha Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Assumptions",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["assumptions"].items())
    lines.extend(["", "## Alpha"])
    lines.extend(f"- {key}: {value}" for key, value in payload["alpha"].items())
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
