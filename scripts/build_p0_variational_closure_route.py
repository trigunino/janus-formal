from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_variational_closure_route.md")
JSON_PATH = Path("outputs/reports/p0_variational_closure_route.json")


VARIATIONAL_REQUIREMENTS = [
    {
        "item": "Interaction action",
        "symbols": ["S_int[g_plus,g_minus,e_plus,e_minus,psi_plus,psi_minus]"],
        "required_identity": "delta S_int must generate K_plus, K_minus, and Q_cross from one covariant functional",
        "status": "missing",
    },
    {
        "item": "Euler-Lagrange closure",
        "symbols": ["delta S/delta g_plus", "delta S/delta g_minus", "delta S/delta e_plus", "delta S/delta e_minus"],
        "required_identity": "field variations must yield the proposed interaction tensors without external algebraic patches",
        "status": "missing",
    },
    {
        "item": "Diffeomorphism Noether identity",
        "symbols": ["nabla_plus K_plus", "nabla_minus K_minus", "Bianchi identity"],
        "required_identity": "diagonal diffeomorphism invariance must imply the two-sector Bianchi residual cancellation",
        "status": "missing",
    },
    {
        "item": "Stress-energy variation",
        "symbols": ["T_plus", "T_minus", "K_plus", "K_minus"],
        "required_identity": "metric or tetrad variation must define stress-energy consistently in both sectors",
        "status": "missing",
    },
    {
        "item": "Symmetry constraints",
        "symbols": ["K_plus_munu", "K_minus_munu", "Q_cross", "L"],
        "required_identity": "interaction tensors must be symmetric, covariant, and compatible with the same L map used by Q_cross",
        "status": "missing",
    },
]


def build_payload() -> dict:
    return {
        "description": (
            "Bounded P0 route check: can Janus K_plus/K_minus and Q_cross be "
            "derived from an interaction action or bimetric/tetrad variational principle?"
        ),
        "route": "variational-action-closure",
        "status": "open-not-derived",
        "action_supplied": False,
        "euler_lagrange_identities_supplied": False,
        "noether_bianchi_identity_supplied": False,
        "stress_energy_variation_supplied": False,
        "symmetry_constraints_supplied": False,
        "allows_fitted_potentials": False,
        "source_derived_relation": {
            "required": "F = D L must follow from the same source-derived action/transport variation",
            "not_allowed": "fit an interaction potential and then tune K or Q_cross independently",
            "status": "open",
        },
        "required_identities": VARIATIONAL_REQUIREMENTS,
        "acceptance_gate": [
            "supply a covariant interaction action",
            "derive K_plus and K_minus by metric or tetrad variation",
            "derive Q_cross from the same variational data, not a separate optical fit",
            "prove the diffeomorphism/Bianchi Noether identity",
            "show F = D L is source-derived and compatible with K/Q_cross",
            "satisfy symmetry and tensor covariance constraints",
            "introduce no fitted potentials or survey-normalized amplitudes",
        ],
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A variational route is admissible as a research branch, but it does not "
            "unlock predictions until the action and all listed identities are supplied."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Variational Closure Route",
        "",
        payload["description"],
        "",
        f"Route: {payload['route']}",
        f"Status: {payload['status']}",
        f"Action supplied: {payload['action_supplied']}",
        f"Euler-Lagrange identities supplied: {payload['euler_lagrange_identities_supplied']}",
        f"Noether/Bianchi identity supplied: {payload['noether_bianchi_identity_supplied']}",
        f"Stress-energy variation supplied: {payload['stress_energy_variation_supplied']}",
        f"Symmetry constraints supplied: {payload['symmetry_constraints_supplied']}",
        f"Allows fitted potentials: {payload['allows_fitted_potentials']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Required Variational Identities",
        "",
        "| item | symbols | required identity | status |",
        "|---|---|---|---|",
    ]
    for row in payload["required_identities"]:
        symbols = ", ".join(f"`{symbol}`" for symbol in row["symbols"])
        lines.append(f"| {row['item']} | {symbols} | {row['required_identity']} | {row['status']} |")
    relation = payload["source_derived_relation"]
    lines.extend(
        [
            "",
            "## Source-Derived Relation",
            "",
            f"Required: {relation['required']}",
            f"Not allowed: {relation['not_allowed']}",
            f"Status: {relation['status']}",
            "",
            "## Acceptance Gate",
            "",
        ]
    )
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
