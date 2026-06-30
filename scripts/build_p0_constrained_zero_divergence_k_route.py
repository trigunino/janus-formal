from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_constrained_zero_divergence_k_route.md")
JSON_PATH = Path("outputs/reports/p0_constrained_zero_divergence_k_route.json")


CONSTRAINTS = [
    {
        "item": "Zero divergence plus",
        "condition": "nabla_plus_nu K_plus^{mu nu} = 0",
        "status": "required",
    },
    {
        "item": "Zero divergence minus",
        "condition": "nabla_minus_nu K_minus^{mu nu} = 0",
        "status": "required",
    },
    {
        "item": "Symmetry",
        "condition": "K_plus^{mu nu}=K_plus^{nu mu} and K_minus^{mu nu}=K_minus^{nu mu}",
        "status": "required",
    },
    {
        "item": "Same L/Q_cross compatibility",
        "condition": "K_plus, K_minus, and Q_cross must be generated from the same L map",
        "status": "required",
    },
    {
        "item": "Boundary and gauge conditions",
        "condition": "well-posed boundary data plus gauge fixing for residual transverse freedom",
        "status": "required",
    },
]


def build_payload() -> dict:
    return {
        "description": (
            "Bounded P0 route: solve K_plus/K_minus as minimizers of a covariant "
            "local functional under zero-divergence and compatibility constraints."
        ),
        "route": "constrained-variational-zero-divergence-k",
        "status": "proposal-open-new-axiom-risk",
        "functional": {
            "type": "covariant-local",
            "unknowns": ["K_plus^{mu nu}", "K_minus^{mu nu}", "L"],
            "objective": (
                "minimize I[K_plus,K_minus,L] locally and covariantly, without "
                "using survey likelihoods or observational amplitudes"
            ),
        },
        "constraints": CONSTRAINTS,
        "forbidden_shortcuts": [
            "observational fit",
            "survey-normalized potential",
            "independent Q_cross tuning",
            "post-hoc non-covariant gauge patch",
        ],
        "source_derived": False,
        "new_axiom_risk": True,
        "prediction_ready": False,
        "physics_closed": False,
        "acceptance_gate": [
            "state the local covariant functional explicitly",
            "derive Euler-Lagrange equations for K_plus, K_minus, and L",
            "prove nabla_plus K_plus=0 and nabla_minus K_minus=0 as enforced constraints",
            "prove symmetry of both K tensors",
            "prove compatibility with the same L used for Q_cross",
            "state boundary and gauge conditions that make the solve well posed",
            "show no observational fit or survey-normalized amplitude enters",
        ],
        "verdict": (
            "This is a bounded solver route, not a source-derived closure. It may "
            "organize the K problem, but the variational functional is an added "
            "principle until independently derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Constrained Zero-Divergence K Route",
        "",
        payload["description"],
        "",
        f"Route: {payload['route']}",
        f"Status: {payload['status']}",
        f"Functional type: {payload['functional']['type']}",
        f"Source derived: {payload['source_derived']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Objective",
        "",
        payload["functional"]["objective"],
        "",
        "## Constraints",
        "",
        "| item | condition | status |",
        "|---|---|---|",
    ]
    for row in payload["constraints"]:
        lines.append(f"| {row['item']} | `{row['condition']}` | {row['status']} |")
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Acceptance Gate", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_gate"])
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
