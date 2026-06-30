from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.check_symbolic_formulas import check_boosted_perfect_fluid_t00
from scripts.build_p0_stueckelberg_beta_field_provenance_gate import (
    build_payload as build_beta_gate_payload,
)


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_noncomoving_source_identity_target.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_noncomoving_source_identity_target.json")


def build_payload() -> dict:
    boosted_check = check_boosted_perfect_fluid_t00()
    beta_gate = build_beta_gate_payload()["decision"]
    formula = {
        "stress_tensor": "T^{mu nu}=(rho+p)u^mu u^nu+p g^{mu nu}+Pi^{mu nu}",
        "positive_frame_t00": "T00=(rho+p)gamma^2-p+Pi00",
        "dust_limit": "p=0, Pi00=0 gives T00=rho gamma^2",
        "comoving_limit": "gamma=1, Pi00=0 gives T00=rho",
    }
    closure_requirements = [
        "source-derived gamma field for u_minus_to_plus in the positive frame",
        "pressure/equation-of-state branch p_minus_to_plus",
        "Pi00 transport or proof Pi00=0",
        "Q_det/Q_cross convention applied once, not as scalar absorption of velocity terms",
        "Bianchi-compatible momentum equations for T0i, not only T00",
    ]
    decision = {
        "boosted_t00_formula_checked": boosted_check.ok,
        "noncomoving_source_identity_target_defined": True,
        "local_gamma_u_t00_code_available": True,
        "beta_field_provenance_gate_available": beta_gate["beta_field_gate_defined"],
        "source_derived_beta_available": beta_gate["source_derived_beta_available"],
        "noncomoving_source_identity_closed": False,
        "prediction_ready": False,
    }
    return {
        "artifact": "p0_stueckelberg_noncomoving_source_identity_target",
        "status": "noncomoving-source-identity-target-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "symbolic_check": {
            "name": boosted_check.name,
            "ok": boosted_check.ok,
            "expression": boosted_check.expression,
        },
        "code_surfaces": [
            "janus_lab.lensing.lorentz_gamma_from_beta_vectors",
            "janus_lab.lensing.transported_four_velocity_from_beta_vectors",
            "janus_lab.lensing.boosted_perfect_fluid_t00_source",
            "janus_lab.lensing.positive_noncomoving_t00_source_grid",
            "scripts.build_p0_stueckelberg_beta_field_provenance_gate",
        ],
        "formula": formula,
        "closure_requirements": closure_requirements,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    check = payload["symbolic_check"]
    lines = [
        "# P0 Stueckelberg Noncomoving Source Identity Target",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Symbolic Check",
        f"- {check['name']}: ok={check['ok']}; expression=`{check['expression']}`",
        "",
        "## Formula",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["formula"].items())
    lines.extend(["", "## Code Surfaces"])
    lines.extend(f"- `{item}`" for item in payload["code_surfaces"])
    lines.extend(["", "## Closure Requirements"])
    lines.extend(f"- {item}" for item in payload["closure_requirements"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Boosted T00 formula checked: {decision['boosted_t00_formula_checked']}",
            f"Noncomoving source identity target defined: {decision['noncomoving_source_identity_target_defined']}",
            f"Local gamma/u/T00 code available: {decision['local_gamma_u_t00_code_available']}",
            f"Beta field provenance gate available: {decision['beta_field_provenance_gate_available']}",
            f"Source-derived beta available: {decision['source_derived_beta_available']}",
            f"Noncomoving source identity closed: {decision['noncomoving_source_identity_closed']}",
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
