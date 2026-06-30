from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_two_diffeo_route.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_two_diffeo_route.json")


MAP_OPTIONS = [
    {
        "field": "phi_minus_to_plus",
        "type": "inter-sector diffeomorphism",
        "definition": "phi_minus_to_plus: M_plus -> M_minus pulls minus-sector fields into plus coordinates",
        "role": "Stueckelberg map restoring plus-sector covariance of cross couplings",
        "status": "candidate-new-axiom",
    },
    {
        "field": "L_minus_to_plus",
        "type": "tetrad/Lorentz map",
        "definition": "L_minus_to_plus^A_B maps minus tetrad components to plus tetrad components",
        "role": "local Stueckelberg solder field for K_plus/K_minus and Q_cross",
        "status": "candidate-new-axiom",
    },
]


SPLIT_NOETHER_IDENTITIES = [
    {
        "sector": "plus",
        "identity": "nabla_plus_mu(E_plus^{mu}_{nu}+K_plus^{mu}_{nu}) + E_phi dot partial_nu phi_minus_to_plus + E_L dot D_plus_nu L = 0",
        "closure_target": "with E_phi=0 and E_L=0, produce R_plus_nu=0 separately",
        "status": "candidate",
    },
    {
        "sector": "minus",
        "identity": "nabla_minus_mu(E_minus^{mu}_{nu}+K_minus^{mu}_{nu}) + pulled-back E_phi terms + E_L dot D_minus_nu L^{-1} = 0",
        "closure_target": "with E_phi=0 and E_L=0, produce R_minus_nu=0 separately",
        "status": "candidate",
    },
]


REQUIRED_EQUATIONS = [
    "delta S/delta phi_minus_to_plus = 0 or equivalent map equation",
    "delta S/delta phi_plus_to_minus = 0 if mirror diffeomorphism is independent",
    "delta S/delta L_minus_to_plus = 0 or equivalent tetrad-map equation",
    "delta S/delta L_plus_to_minus = 0 if inverse/mirror L is not imposed",
    "constraints enforcing phi inverse consistency or declaring orientation of one active map",
    "constraints enforcing L_plus_to_minus=L_minus_to_plus^{-1} or source-derived mirror relation",
]


ACTION_SKELETON = [
    "S = S_plus[g_plus,matter_plus] + S_minus[g_minus,matter_minus] + S_cross",
    "S_cross = int sqrt(|g_plus|) L_cross(g_plus, phi^*g_minus, L, matter_plus, phi^*matter_minus)",
    "phi and L must enter S_cross as variational fields, not as prescribed background maps",
    "inverse constraints may be imposed only if their multipliers are part of the action",
]


FORMAL_NOETHER_RESULT = [
    "plus diffeo invariance gives nabla_plus(E_plus+K_plus)+E_phi dphi+E_L D_plus L=0",
    "minus diffeo invariance gives nabla_minus(E_minus+K_minus)+mirror E_phi/E_L terms=0",
    "if E_phi=0 and E_L=0 are source-derived, the identities can close R_plus and R_minus",
    "covariance alone supplies identities, not a unique phi or L selector",
]


SELECTION_OBSTRUCTION = [
    "S_cross must be fixed by Janus source/action data; otherwise E_phi/E_L are chosen by hand",
    "two-diffeomorphism symmetry removes gauge redundancy but does not choose a representative",
    "inverse phi/L constraints reduce variables but do not determine the physical branch",
    "boundary/gauge conditions are still needed for uniqueness of phi, J_phi and L",
]


def build_payload() -> dict:
    return {
        "description": (
            "Bounded P0 route: treat the inter-sector diffeomorphism phi or tetrad "
            "map L as a Stueckelberg field so two-sector covariance can yield split "
            "Noether identities for R_plus=0 and R_minus=0."
        ),
        "route": "stueckelberg-two-diffeomorphism-closure",
        "status": "open-new-axiom-candidate",
        "new_axiom": True,
        "source_derived": False,
        "two_sector_covariance_restored": "candidate",
        "split_noether_identities_derived": False,
        "map_equations_supplied": False,
        "same_l_for_k_and_qcross": True,
        "same_l_requirement": (
            "The L field used in K_plus/K_minus transport must be the same L used "
            "in Q_cross optical contractions; no independent optical map is allowed."
        ),
        "map_options": MAP_OPTIONS,
        "action_skeleton": ACTION_SKELETON,
        "formal_noether_result": FORMAL_NOETHER_RESULT,
        "candidate_split_noether_identities": SPLIT_NOETHER_IDENTITIES,
        "required_equations": REQUIRED_EQUATIONS,
        "selection_obstruction": SELECTION_OBSTRUCTION,
        "acceptance_gate": [
            "write a covariant two-sector action S[g_plus,g_minus,phi,L,matter]",
            "derive deltaS/delta phi or deltaS/delta L map equations",
            "prove plus and minus diffeomorphism variations are independent after Stueckelberg restoration",
            "show the on-shell map equations reduce the plus identity to R_plus=0",
            "show the on-shell map equations reduce the minus identity to R_minus=0",
            "use the same L for K transport and Q_cross",
            "replace new_axiom=true only if the map/action is source-derived later",
        ],
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The route is innovative and bounded, but remains a new axiom candidate "
            "until the Stueckelberg map equations and split Noether identities are "
            "derived from a source-backed action."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Two-Diffeomorphism Route",
        "",
        payload["description"],
        "",
        f"Route: {payload['route']}",
        f"Status: {payload['status']}",
        f"New axiom: {payload['new_axiom']}",
        f"Source derived: {payload['source_derived']}",
        f"Two-sector covariance restored: {payload['two_sector_covariance_restored']}",
        f"Split Noether identities derived: {payload['split_noether_identities_derived']}",
        f"Map equations supplied: {payload['map_equations_supplied']}",
        f"Same L for K and Q_cross: {payload['same_l_for_k_and_qcross']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Map Options",
        "",
        "| field | type | definition | role | status |",
        "|---|---|---|---|---|",
    ]
    for row in payload["map_options"]:
        lines.append(
            f"| `{row['field']}` | {row['type']} | {row['definition']} | {row['role']} | {row['status']} |"
        )
    lines.extend(["", "## Action Skeleton", ""])
    lines.extend(f"- `{item}`" for item in payload["action_skeleton"])
    lines.extend(["", "## Formal Noether Result", ""])
    lines.extend(f"- `{item}`" for item in payload["formal_noether_result"])
    lines.extend(["", "## Candidate Split Noether Identities", ""])
    lines.extend(
        f"- {row['sector']}: `{row['identity']}`; target: {row['closure_target']} ({row['status']})"
        for row in payload["candidate_split_noether_identities"]
    )
    lines.extend(["", "## Required Equations", ""])
    lines.extend(f"- `{item}`" for item in payload["required_equations"])
    lines.extend(["", "## Selection Obstruction", ""])
    lines.extend(f"- {item}" for item in payload["selection_obstruction"])
    lines.extend(
        [
            "",
            "## Same-L Requirement",
            "",
            payload["same_l_requirement"],
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
