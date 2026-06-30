from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.check_symbolic_formulas import check_zero_anisotropic_stress_lensing_potential


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_gauge_slip_branch.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_gauge_slip_branch.json")


def build_payload() -> dict:
    slip_check = check_zero_anisotropic_stress_lensing_potential()
    branch = {
        "gauge": "scalar weak-field/Newtonian-gauge branch",
        "metric": "ds^2=-(1+2 Phi)dt^2+(1-2 Psi)delta_ij dx^i dx^j",
        "lensing_potential": "Phi_lens=(Phi+Psi)/2",
        "zero_anisotropic_stress_limit": "Phi=Psi implies Phi_lens=Phi",
    }
    blockers = [
        "derive the gauge from Janus perturbations rather than impose it globally",
        "derive the Janus slip equation Phi-Psi from pressure/Pi and cross-sector stress",
        "do not set Phi=Psi when transported Pi_minus_to_plus is nonzero or unknown",
        "do not use this scalar branch for vector/tensor perturbations or full lensing closure",
    ]
    decision = {
        "zero_anisotropic_stress_slip_check_passed": slip_check.ok,
        "gauge_branch_declared": True,
        "janus_slip_equation_derived": False,
        "full_metric_potential_closure": False,
        "prediction_ready": False,
    }
    return {
        "artifact": "p0_stueckelberg_gauge_slip_branch",
        "status": "gauge-slip-branch-partial",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "symbolic_check": {
            "name": slip_check.name,
            "ok": slip_check.ok,
            "expression": slip_check.expression,
        },
        "branch": branch,
        "blockers": blockers,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    check = payload["symbolic_check"]
    lines = [
        "# P0 Stueckelberg Gauge Slip Branch",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Symbolic Check",
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
            f"Zero anisotropic stress slip check passed: {decision['zero_anisotropic_stress_slip_check_passed']}",
            f"Gauge branch declared: {decision['gauge_branch_declared']}",
            f"Janus slip equation derived: {decision['janus_slip_equation_derived']}",
            f"Full metric potential closure: {decision['full_metric_potential_closure']}",
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
