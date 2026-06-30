from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_spinless_moments_slip_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_spinless_moments_slip_target.json")


def build_payload() -> dict:
    moments = {
        "moment0_density": "rho_other_to_self = B4vol * rho_other with receiver mass-shell normalization",
        "continuity": "no direct torsion force/source for minimal spinless Vlasov; volume flux conserved conditionally",
        "moment1_flux": "Euler flux changes only through metric geodesic/lapse projection",
        "moment2_pressure_pi": "p and Pi are moments of transported f; Pi=0 only for isotropic f, not automatic",
    }
    slip = {
        "metric_gauge": "ds^2=-(1+2Phi)dt^2+a^2(1-2Psi)dx^2",
        "target_formula": "Psi|Sigma - Phi|Sigma = (3/2)*H*(beta*Delta_chi + lambda)",
        "after_run1_substitution": "beta*Delta_chi=-sigma*(1+tau)/2 and lambda=-4*q_T",
        "status": "target-from-perturbed-Palatini-jump-not-derived",
    }
    theorem_status = {
        "spinless_moment0_density_written": True,
        "spinless_continuity_conditionally_closed": True,
        "spinless_flux_euler_structured": True,
        "pressure_pi_moments_defined": True,
        "pi_isotropy_not_assumed": True,
        "slip_formula_target_encoded": True,
        "slip_formula_derived_from_field_equations": False,
        "lensing_growth_sources_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive the slip formula from perturbed Einstein-Palatini jump equations",
        "compute Pi from transported distribution f rather than assuming Pi=0",
        "insert slip into lensing potential Phi+Psi and growth source",
    ]
    return {
        "description": "Spinless Vlasov moment cascade and boundary slip target.",
        "status": "moments-structured-slip-open",
        "moments": moments,
        "slip": slip,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "Spinless moments are structurally ready with active B4vol measure. The boundary "
            "slip formula is now the key observable target, but still must be derived from "
            "perturbed field-jump equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Spinless Moments Slip Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Moments",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["moments"].items())
    lines.extend(["", "## Slip"])
    lines.extend(f"- {key}: {value}" for key, value in payload["slip"].items())
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
