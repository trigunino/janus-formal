from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_optimal_transport_matching_route.md")
JSON_PATH = Path("outputs/reports/p0_optimal_transport_matching_route.json")


MATCHING_CONDITIONS = [
    {
        "item": "Mass/measure matching",
        "condition": "phi_* mu_plus = mu_minus, with mu fixed by Janus sector sources rather than observations",
        "status": "required",
    },
    {
        "item": "Covariant optimal transport",
        "condition": "phi extremizes a covariant transport cost C[g_plus,g_minus,L,mu_plus,mu_minus]",
        "status": "new-axiom-risk",
    },
    {
        "item": "Monge-Ampere-like constraint",
        "condition": "det(D phi) sqrt(|g_minus(phi)|) rho_minus(phi) = sqrt(|g_plus|) rho_plus",
        "status": "candidate",
    },
    {
        "item": "Same phi/L closure",
        "condition": "K_plus, K_minus, and Q_cross must all be computed from the same phi/L",
        "status": "required",
    },
    {
        "item": "Bianchi compatibility",
        "condition": "the matching equations must imply the plus/minus K residual identities and Q_cross balance",
        "status": "open",
    },
]


def build_payload() -> dict:
    return {
        "description": (
            "Bounded P0 route: explore phi as a mass/measure matching map between "
            "Janus sectors, using covariant optimal transport or a Monge-Ampere-like "
            "constraint to derive K_plus/K_minus and Q_cross from the same phi/L."
        ),
        "route": "optimal-transport-geometric-matching",
        "status": "proposal-open-new-axiom-risk",
        "map": {
            "symbol": "phi: M_plus -> M_minus",
            "role": "mass/measure matching map between sectors",
            "induced_l": "L = d phi or tetrad-projected differential of phi",
        },
        "candidate_equations": {
            "measure_pushforward": "phi_* mu_plus = mu_minus",
            "transport_stationarity": "delta_phi C[g_plus,g_minus,L,mu_plus,mu_minus] = 0",
            "monge_ampere_constraint": (
                "det(D phi) sqrt(|g_minus(phi)|) rho_minus(phi) = sqrt(|g_plus|) rho_plus"
            ),
        },
        "closure_targets": [
            "derive K_plus from variation or stress of the same phi/L matching rule",
            "derive K_minus from the transported dual of the same phi/L matching rule",
            "derive Q_cross from the same induced L, not from a separate fit",
            "prove the plus/minus Bianchi residual cancellations",
        ],
        "matching_conditions": MATCHING_CONDITIONS,
        "forbidden_shortcuts": [
            "fit phi to observations",
            "fit transport cost to survey residuals",
            "choose K_plus or K_minus independently of phi/L",
            "tune Q_cross separately from the induced L",
        ],
        "source_derived": False,
        "new_axiom_risk": True,
        "prediction_ready": False,
        "physics_closed": False,
        "acceptance_gate": [
            "derive the sector measures mu_plus and mu_minus from Janus sources",
            "state a covariant transport cost or Monge-Ampere-like constraint",
            "derive phi and L without observational fitting",
            "derive K_plus, K_minus, and Q_cross from the same phi/L",
            "prove covariance, symmetry, and Bianchi compatibility",
            "keep all amplitudes source-derived rather than survey-normalized",
        ],
        "verdict": (
            "This is a bounded geometric matching route, not a prediction input. "
            "It remains a new-axiom-risk branch until the transport rule and "
            "sector measures are derived from Janus sources."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Optimal-Transport Matching Route",
        "",
        payload["description"],
        "",
        f"Route: {payload['route']}",
        f"Status: {payload['status']}",
        f"Map: {payload['map']['symbol']}",
        f"Map role: {payload['map']['role']}",
        f"Induced L: {payload['map']['induced_l']}",
        f"Source derived: {payload['source_derived']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Candidate Equations",
        "",
    ]
    for key, equation in payload["candidate_equations"].items():
        lines.append(f"- {key}: `{equation}`")
    lines.extend(
        [
            "",
            "## Matching Conditions",
            "",
            "| item | condition | status |",
            "|---|---|---|",
        ]
    )
    for row in payload["matching_conditions"]:
        lines.append(f"| {row['item']} | `{row['condition']}` | {row['status']} |")
    lines.extend(["", "## Closure Targets", ""])
    lines.extend(f"- {item}" for item in payload["closure_targets"])
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
