from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.check_symbolic_formulas import check_comoving_perfect_fluid_t00_density_only


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_source_identity_branch.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_source_identity_branch.json")


def build_payload() -> dict:
    t00_check = check_comoving_perfect_fluid_t00_density_only()
    admissible_reduction = {
        "branch": "weak-field comoving scalar source",
        "condition_1": "u_plus and transported u_minus_to_plus are comoving in the positive frame",
        "condition_2": "Pi00_plus=Pi00_minus_to_plus=0 from orthogonality, not by fit",
        "condition_3": "pressure contributes to slip/spatial equations, not directly to comoving T00",
        "condition_4": "delta S00_plus=rho_plus-rho_minus_eff with declared Q_det/Q_cross convention",
    }
    open_cases = [
        "non-comoving transported velocity adds gamma^2(rho+p) and momentum terms",
        "nonzero Pi00 or imperfect transport invalidates scalar rho_eff reduction",
        "pressure gradients still affect gauge/slip and Bianchi closure",
        "Q_det/Q_cross provenance must be declared before source identity is used",
    ]
    decision = {
        "comoving_t00_density_check_passed": t00_check.ok,
        "source_identity_defined_for_comoving_scalar_branch": True,
        "general_source_identity_closed": False,
        "pressure_pi_general_case_closed": False,
        "prediction_ready": False,
    }
    return {
        "artifact": "p0_stueckelberg_source_identity_branch",
        "status": "source-identity-branch-partial",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "symbolic_check": {
            "name": t00_check.name,
            "ok": t00_check.ok,
            "expression": t00_check.expression,
        },
        "admissible_reduction": admissible_reduction,
        "open_cases": open_cases,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    check = payload["symbolic_check"]
    lines = [
        "# P0 Stueckelberg Source Identity Branch",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Symbolic Check",
        f"- {check['name']}: ok={check['ok']}; expression=`{check['expression']}`",
        "",
        "## Admissible Reduction",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["admissible_reduction"].items())
    lines.extend(["", "## Open Cases"])
    lines.extend(f"- {item}" for item in payload["open_cases"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Comoving T00 density check passed: {decision['comoving_t00_density_check_passed']}",
            f"Source identity defined for comoving scalar branch: {decision['source_identity_defined_for_comoving_scalar_branch']}",
            f"General source identity closed: {decision['general_source_identity_closed']}",
            f"Pressure/Pi general case closed: {decision['pressure_pi_general_case_closed']}",
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
