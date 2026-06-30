from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_phi_j_l_intrinsic_selector_attempt.md")
JSON_PATH = Path("outputs/reports/p0_phi_j_l_intrinsic_selector_attempt.json")


def build_payload() -> dict:
    epsilon = sp.symbols("epsilon", real=True)
    distortion_energy = sp.pi * epsilon**2
    stationarity = sp.diff(distortion_energy, epsilon)
    solutions = sp.solve([stationarity], [epsilon], dict=True)
    second_derivative = sp.diff(distortion_energy, epsilon, 2)
    harmonic_residual_norm = sp.pi * epsilon**2
    rows = [
        {
            "selector": "minimal_distortion",
            "functional": "Integral_0^{2pi} (J-1)^2 dx = pi epsilon^2",
            "solution": str(solutions),
            "selects_unique": True,
            "source_derived": False,
        },
        {
            "selector": "harmonic_map_regularizer",
            "functional": "Integral_0^{2pi} (phi''(x))^2 dx = pi epsilon^2",
            "solution": str(sp.solve([sp.diff(harmonic_residual_norm, epsilon)], [epsilon], dict=True)),
            "selects_unique": True,
            "source_derived": False,
        },
        {
            "selector": "mirror_periodic_boundary",
            "functional": "periodicity + inverse orientation",
            "solution": "open family |epsilon|<1",
            "selects_unique": False,
            "source_derived": True,
        },
    ]
    return {
        "description": "Internal attempt to select phi/J/L by intrinsic no-fit variational criteria.",
        "status": "intrinsic-selector-selects-toy-map-new-principle",
        "candidate_family": "phi=x+epsilon sin(x)",
        "distortion_energy": str(distortion_energy),
        "stationarity_equation": str(stationarity),
        "stationarity_solutions": str(solutions),
        "second_derivative": str(second_derivative),
        "rows": rows,
        "intrinsic_selector_fixes_toy_family": True,
        "selected_epsilon": 0,
        "uses_observational_fit": False,
        "source_derived_from_janus": False,
        "new_axiom_risk": True,
        "can_use_as_published_janus_closure": False,
        "can_use_as_candidate_research_principle": True,
        "physics_closed": False,
        "prediction_ready": False,
        "acceptance_before_use": [
            "derive the functional from Janus action/source equations",
            "prove covariance beyond the 1D toy family",
            "prove mirror plus/minus compatibility",
            "prove the selected map closes R_plus and R_minus with B4vol and D L",
        ],
        "verdict": (
            "I can construct a no-fit intrinsic selector that fixes the toy family, but it is "
            "not yet Janus-derived. Using it as closure would be a new mathematical principle "
            "unless derived from the published/source equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Phi/J/L Intrinsic Selector Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate family: `{payload['candidate_family']}`",
        f"Distortion energy: `{payload['distortion_energy']}`",
        f"Stationarity equation: `{payload['stationarity_equation']}`",
        f"Stationarity solutions: `{payload['stationarity_solutions']}`",
        f"Selected epsilon: {payload['selected_epsilon']}",
        f"Intrinsic selector fixes toy family: {payload['intrinsic_selector_fixes_toy_family']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Source-derived from Janus: {payload['source_derived_from_janus']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Can use as published Janus closure: {payload['can_use_as_published_janus_closure']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rows",
        "",
        "| selector | functional | solution | selects unique | source derived |",
        "|---|---|---|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['selector']} | `{row['functional']}` | `{row['solution']}` | "
            f"{row['selects_unique']} | {row['source_derived']} |"
        )
    lines.extend(["", "## Acceptance Before Use", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_before_use"])
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
