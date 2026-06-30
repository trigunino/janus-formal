from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.check_symbolic_formulas import (
    check_comoving_perfect_fluid_t00_density_only,
    check_linearized_00_poisson_normalization,
    check_zero_anisotropic_stress_lensing_potential,
)


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_comoving_scalar_metric_closure_candidate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_comoving_scalar_metric_closure_candidate.json")


def build_payload() -> dict:
    checks = {
        "linearized_00_poisson_normalization": check_linearized_00_poisson_normalization().ok,
        "zero_anisotropic_stress_slip": check_zero_anisotropic_stress_lensing_potential().ok,
        "comoving_t00_density_only": check_comoving_perfect_fluid_t00_density_only().ok,
    }
    assumptions = [
        "scalar weak-field branch",
        "positive optical receiver metric",
        "comoving transported source velocities",
        "Pi00_plus=Pi00_minus_to_plus=0",
        "Phi=Psi from zero anisotropic stress",
        "rho_minus_eff already includes declared Q_det/Q_cross convention",
    ]
    derived_chain = [
        "delta G00_plus=2 Delta Psi_plus",
        "delta G00_plus=8 pi G delta S00_plus",
        "delta S00_plus=rho_plus-rho_minus_eff",
        "Phi=Psi and Phi_lens_plus=(Phi+Psi)/2=Phi",
        "Delta Phi_lens_plus=4 pi G (rho_plus-rho_minus_eff)",
    ]
    exclusions = [
        "non-comoving velocities",
        "nonzero anisotropic stress",
        "pressure-gradient slip",
        "generic tensor perturbations",
        "survey normalization or fitted shear amplitude",
    ]
    restricted_closure = all(checks.values())
    decision = {
        "restricted_comoving_scalar_closure_candidate_passed": restricted_closure,
        "promotes_poisson_to_metric_for_restricted_branch": restricted_closure,
        "general_metric_potential_closed": False,
        "prediction_ready": False,
    }
    return {
        "artifact": "p0_stueckelberg_comoving_scalar_metric_closure_candidate",
        "status": "restricted-comoving-scalar-closure-candidate",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "checks": checks,
        "assumptions": assumptions,
        "derived_chain": derived_chain,
        "exclusions": exclusions,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Comoving Scalar Metric Closure Candidate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Checks",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["checks"].items())
    lines.extend(["", "## Assumptions"])
    lines.extend(f"- {item}" for item in payload["assumptions"])
    lines.extend(["", "## Derived Chain"])
    lines.extend(f"- `{item}`" for item in payload["derived_chain"])
    lines.extend(["", "## Exclusions"])
    lines.extend(f"- {item}" for item in payload["exclusions"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Restricted comoving scalar closure candidate passed: {decision['restricted_comoving_scalar_closure_candidate_passed']}",
            f"Promotes Poisson to metric for restricted branch: {decision['promotes_poisson_to_metric_for_restricted_branch']}",
            f"General metric potential closed: {decision['general_metric_potential_closed']}",
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
