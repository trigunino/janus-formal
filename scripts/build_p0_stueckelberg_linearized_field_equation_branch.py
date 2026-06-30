from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.check_symbolic_formulas import check_linearized_00_poisson_normalization


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_linearized_field_equation_branch.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_linearized_field_equation_branch.json")


def build_payload() -> dict:
    normalization_check = check_linearized_00_poisson_normalization()
    branch = {
        "metric_assumption": "weak-field scalar branch h00=-2 Phi, hij=2 Psi delta_ij",
        "linearized_00": "delta G00_plus = 2 Delta Psi_plus",
        "field_equation": "delta G00_plus = chi delta S00_plus",
        "poisson_limit": "Delta Psi_plus = 4 pi G rho_eff_plus when chi=8 pi G",
        "source_anchor": "M15/M30 weak-field signed source rho_eff_plus=rho_plus-rho_minus_eff",
    }
    blockers = [
        "derive the scalar gauge from the Janus metric perturbation, not only assume it",
        "derive Phi_lens_plus=(Phi+Psi) or a Janus replacement before optical use",
        "prove determinant/cross-sector source terms in delta S00_plus match rho_eff_plus",
        "extend beyond scalar weak-field before claiming full tensor lensing",
    ]
    decision = {
        "linearized_00_poisson_normalization_checked": normalization_check.ok,
        "janus_linearized_field_equation_derived": False,
        "gauge_assumption_closed": False,
        "source_identity_closed": False,
        "prediction_ready": False,
    }
    return {
        "artifact": "p0_stueckelberg_linearized_field_equation_branch",
        "status": "linearized-field-equation-branch-partial",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "normalization_check": {
            "name": normalization_check.name,
            "ok": normalization_check.ok,
            "expression": normalization_check.expression,
        },
        "branch": branch,
        "blockers": blockers,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    check = payload["normalization_check"]
    lines = [
        "# P0 Stueckelberg Linearized Field Equation Branch",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Normalization Check",
        f"- {check['name']}: ok={check['ok']}; expression=`{check['expression']}`",
        "",
        "## Branch",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["branch"].items())
    lines.extend(["", "## Blockers"])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Linearized 00 Poisson normalization checked: {decision['linearized_00_poisson_normalization_checked']}",
            f"Janus linearized field equation derived: {decision['janus_linearized_field_equation_derived']}",
            f"Gauge assumption closed: {decision['gauge_assumption_closed']}",
            f"Source identity closed: {decision['source_identity_closed']}",
            f"Prediction ready: {decision['prediction_ready']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
