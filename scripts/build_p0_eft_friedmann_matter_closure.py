from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_growth_no_fit_numerical_export import branch_constants, integrate_radion
except ModuleNotFoundError:
    from build_p0_eft_growth_no_fit_numerical_export import branch_constants, integrate_radion


REPORT_PATH = Path("outputs/reports/p0_eft_friedmann_matter_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_friedmann_matter_closure.json")


def derive_omega_m0() -> dict:
    constants = branch_constants()
    radion = integrate_radion(constants)
    omega_t0 = radion[-1]["Omega_T"]
    omega_ds = constants["rho_dS_residual"] / (3.0 * constants["Mpl2"] * constants["H2"])
    omega_m0 = 1.0 - omega_ds - omega_t0
    return {
        "Omega_dS_residual": omega_ds,
        "Omega_T0": omega_t0,
        "Omega_m0": omega_m0,
        "friedmann_sum": omega_m0 + omega_ds + omega_t0,
        "positive_matter_branch": omega_m0 > 0.0,
        "closure_formula": "Omega_m0=1-Omega_dS_residual-Omega_T0",
    }


def build_payload() -> dict:
    closure = derive_omega_m0()
    theorem_status = {
        "friedmann_constraint_encoded": True,
        "mass_shell_flux_enters_matter_density": True,
        "Omega_m0_derived_from_branch": True,
        "positive_matter_branch": closure["positive_matter_branch"],
        "growth_background_matter_closed": closure["positive_matter_branch"],
        "full_cosmology_prediction_ready": False,
    }
    obligations = []
    if not closure["positive_matter_branch"]:
        obligations.append(
            "current branch has non-positive Omega_m0; reduce rho_dS residual, Omega_T0, or change orientation branch"
        )
    return {
        "description": "Friedmann matter closure from Janus dS plus torsion budget.",
        "status": "matter-closure-derived-branch-check",
        "closure": closure,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "Omega_m0 is no longer inserted as 0.3; it is computed from the branch Friedmann "
            "budget. The selected demonstration branch must pass positivity before full "
            "cosmology prediction can be claimed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Friedmann Matter Closure",
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
    if payload["obligations"]:
        lines.extend(["", "## Obligations"])
        lines.extend(f"- {item}" for item in payload["obligations"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
