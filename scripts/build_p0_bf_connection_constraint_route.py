from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_bf_connection_constraint_route.md")
JSON_PATH = Path("outputs/reports/p0_bf_connection_constraint_route.json")


CONSTRAINT_TARGETS = [
    {
        "item": "Relative connection curvature",
        "field": "Omega_alpha",
        "constraint": "R_Omega_{alpha beta}=0 or R_Omega fixed by source-derived relative curvature",
        "purpose": "test whether L transport can be closed without fitting path data",
    },
    {
        "item": "L multiplier equation",
        "field": "lambda_L",
        "constraint": "delta S_BF/delta lambda_L enforces D_alpha L - Omega_alpha L = 0",
        "purpose": "make L an Euler-Lagrange field, not an algebraic patch",
    },
    {
        "item": "Divergence constraint",
        "field": "B_plus/B_minus",
        "constraint": "nabla_plus K_plus=0 and nabla_minus K_minus=0",
        "purpose": "separate R_plus/R_minus closure from observational normalization",
    },
    {
        "item": "Same L compatibility",
        "field": "L",
        "constraint": "the same L must generate K_plus, K_minus, and Q_cross",
        "purpose": "forbid independent K/Q_cross tuning",
    },
]


ACTION_TERMS = [
    "S_curv = int Tr[B wedge (F_Omega - Phi_R[source Janus])]",
    "S_transport = int Tr[Lambda wedge (D L - Omega L)]",
    "S_div = int mu_plus nabla_plus K_plus[L] + mu_minus nabla_minus K_minus[L]",
    "S_cross = int Xi (Q_cross[L] - Q_cross_optical[L])",
]


FORMAL_VARIATIONS = [
    "delta B: F_Omega = Phi_R[source Janus]",
    "delta Lambda: D L - Omega L = 0",
    "delta mu_plus/mu_minus: nabla_plus K_plus[L]=0 and nabla_minus K_minus[L]=0",
    "delta Xi: one same-L Q_cross condition, not an independent scalar amplitude",
    "delta Omega/delta L: adjoint transport equations must reproduce E_L without fitted sources",
]


OPEN_OBSTRUCTIONS = [
    "Phi_R is the decisive missing object: if chosen by hand, the route is a new axiom",
    "flat F_Omega=0 leaves global holonomy/boundary freedom for L",
    "curvature F_Omega fixes Omega only up to gauge unless boundary/gauge is source-selected",
    "multiplier divergence constraints impose closure unless their origin is Janus-derived",
    "K_plus, K_minus and Q_cross must be explicit functionals of the same L",
]


def build_payload() -> dict:
    return {
        "description": (
            "Bounded P0 route: treat the relative connection Omega and L as gauge "
            "fields, with BF/Lagrange multiplier constraints enforcing curvature, "
            "transport, or divergence equations."
        ),
        "route": "bf-connection-constraint-closure",
        "status": "proposal-open-new-axiom-risk",
        "gauge_fields": ["Omega_alpha", "L"],
        "constraint_mechanism": "BF/Lagrange-multiplier",
        "tests_whether": [
            "Euler-Lagrange equations can produce E_L for L transport",
            "R_plus and R_minus can be separated by constrained field equations",
            "K_plus/K_minus and Q_cross can use the same L",
            "closure can proceed without fitted observables or survey-normalized amplitudes",
        ],
        "action_terms": ACTION_TERMS,
        "formal_variations": FORMAL_VARIATIONS,
        "constraint_targets": CONSTRAINT_TARGETS,
        "open_obstructions": OPEN_OBSTRUCTIONS,
        "same_l_for_k_and_qcross": True,
        "allows_fitted_observables": False,
        "full_equations_close": False,
        "new_axiom_risk": True,
        "physics_closed": False,
        "prediction_ready": False,
        "acceptance_gate": [
            "write the complete covariant BF/Lagrange-multiplier action",
            "derive the Euler-Lagrange equation E_L for L",
            "derive Omega equations enforcing R_Omega or a source-derived curvature law",
            "derive divergence constraints without post-hoc tensor patches",
            "prove R_plus and R_minus close separately",
            "prove the same L controls K_plus/K_minus and Q_cross",
            "prove Phi_R is Janus-derived, not a target curvature inserted by hand",
            "show no fitted observables or survey amplitudes enter",
        ],
        "verdict": (
            "This is an out-of-the-box connection constraint route, not a closure "
            "claim. It remains prediction-blocked until the full BF/Lagrange "
            "system closes and derives E_L, R_plus, and R_minus consistently."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 BF Connection Constraint Route",
        "",
        payload["description"],
        "",
        f"Route: {payload['route']}",
        f"Status: {payload['status']}",
        f"Constraint mechanism: {payload['constraint_mechanism']}",
        f"Same L for K/Q_cross: {payload['same_l_for_k_and_qcross']}",
        f"Allows fitted observables: {payload['allows_fitted_observables']}",
        f"Full equations close: {payload['full_equations_close']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Gauge Fields",
        "",
    ]
    lines.extend(f"- `{field}`" for field in payload["gauge_fields"])
    lines.extend(["", "## Candidate Action Terms", ""])
    lines.extend(f"- `{item}`" for item in payload["action_terms"])
    lines.extend(["", "## Formal Variations", ""])
    lines.extend(f"- `{item}`" for item in payload["formal_variations"])
    lines.extend(["", "## Tests Whether", ""])
    lines.extend(f"- {item}" for item in payload["tests_whether"])
    lines.extend(
        [
            "",
            "## Constraint Targets",
            "",
            "| item | field | constraint | purpose |",
            "|---|---|---|---|",
        ]
    )
    for row in payload["constraint_targets"]:
        lines.append(
            f"| {row['item']} | `{row['field']}` | `{row['constraint']}` | {row['purpose']} |"
        )
    lines.extend(["", "## Open Obstructions", ""])
    lines.extend(f"- {item}" for item in payload["open_obstructions"])
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
