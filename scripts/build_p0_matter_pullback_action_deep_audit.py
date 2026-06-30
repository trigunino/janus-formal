from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_stueckelberg_projected_dust_variation_identity import (
    build_payload as build_projected_dust_identity,
)


REPORT_PATH = Path("outputs/reports/p0_matter_pullback_action_deep_audit.md")
JSON_PATH = Path("outputs/reports/p0_matter_pullback_action_deep_audit.json")


def build_payload() -> dict:
    x = sp.symbols("x")
    phi = sp.Function("phi")(x)
    density = sp.Function("F")
    receiver_weight = sp.Function("W")(x)
    dphi = sp.diff(phi, x)

    pure_pullback_lagrangian = density(phi) * dphi
    pure_el = sp.simplify(
        sp.diff(sp.diff(pure_pullback_lagrangian, dphi), x)
        - sp.diff(pure_pullback_lagrangian, phi)
    )
    weighted_lagrangian = receiver_weight * density(phi) * dphi
    weighted_el = sp.simplify(
        sp.diff(sp.diff(weighted_lagrangian, dphi), x)
        - sp.diff(weighted_lagrangian, phi)
    )
    projected_dust = build_projected_dust_identity()
    decision = projected_dust["decision"]
    rows = [
        {
            "route": "pure_top_form_pullback",
            "result": "delta_phi int F(phi) dphi = boundary identity",
            "closed": bool(pure_el == 0),
            "selects_phi_j_l": False,
            "meaning": "a passive pullback of a source matter density is not a map equation",
        },
        {
            "route": "projected_dust_variation",
            "result": "transverse dust divergence gives rho h C(u,u) shape",
            "closed": bool(decision["projected_identity_found"]),
            "selects_phi_j_l": False,
            "meaning": "it supplies the force shape conditionally, not the unique map",
        },
        {
            "route": "receiver_weighted_pullback",
            "result": "delta_phi int W(x) F(phi) dphi gives a nonzero W-gradient term",
            "closed": bool(weighted_el != 0),
            "selects_phi_j_l": False,
            "meaning": "a nonzero map equation requires true receiver/source coupling, not pure pullback",
        },
        {
            "route": "janus_specific_scouple",
            "result": "would need both metrics, same L, B4vol, and matter branch in one action",
            "closed": False,
            "selects_phi_j_l": False,
            "meaning": "not supplied by the current Janus source chain",
        },
    ]
    return {
        "description": "Deep audit of the matter-pullback action route for selecting phi/J/L.",
        "status": "matter-pullback-action-deep-audit-selector-open",
        "pure_pullback_lagrangian": str(pure_pullback_lagrangian),
        "pure_pullback_el_operator": str(pure_el),
        "weighted_pullback_lagrangian": str(weighted_lagrangian),
        "weighted_pullback_el_operator": str(weighted_el),
        "rows": rows,
        "pure_pullback_euler_lagrange_zero": bool(pure_el == 0),
        "pure_matter_pullback_selects_phi_j_l": False,
        "projected_dust_force_shape_derived": bool(decision["projected_identity_found"]),
        "projected_dust_force_shape_conditional": bool(
            decision["dust_connection_residual_closed"] == "conditional"
        ),
        "janus_specific_action_still_required": bool(decision["janus_specific_action_still_required"]),
        "receiver_weighted_term_is_scouple_not_pure_pullback": bool(weighted_el != 0),
        "same_phi_l_selection_derived": False,
        "pressure_pi_extension_closed": False,
        "deep_action_pullback_attempt_completed": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "hidden_axiom_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "what_to_do_with_this": [
            "keep projected dust rho h Cuu as a conditional force-shape result",
            "do not use pure pullback as proof that phi/J/L is selected",
            "search for or derive a genuine receiver/source coupled action",
            "if no such action exists, convert the route into a bounded no-go theorem",
        ],
        "verdict": (
            "The deep pullback audit is useful but negative for selection. Pure matter "
            "pullback is a diffeomorphic top-form identity and has zero phi Euler-Lagrange "
            "operator in the toy model. Dust variation gives the correct projected force "
            "shape conditionally, but a Janus-specific coupled action is still required "
            "to select the same phi/J/L."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Matter Pullback Action Deep Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Pure pullback Lagrangian: `{payload['pure_pullback_lagrangian']}`",
        f"Pure pullback EL operator: `{payload['pure_pullback_el_operator']}`",
        f"Weighted pullback Lagrangian: `{payload['weighted_pullback_lagrangian']}`",
        f"Weighted pullback EL operator: `{payload['weighted_pullback_el_operator']}`",
        f"Pure pullback Euler-Lagrange zero: {payload['pure_pullback_euler_lagrange_zero']}",
        f"Pure matter pullback selects phi/J/L: {payload['pure_matter_pullback_selects_phi_j_l']}",
        f"Projected dust force shape derived: {payload['projected_dust_force_shape_derived']}",
        f"Projected dust force shape conditional: {payload['projected_dust_force_shape_conditional']}",
        f"Janus-specific action still required: {payload['janus_specific_action_still_required']}",
        (
            "Receiver-weighted term is S_couple not pure pullback: "
            f"{payload['receiver_weighted_term_is_scouple_not_pure_pullback']}"
        ),
        f"Same phi/L selection derived: {payload['same_phi_l_selection_derived']}",
        f"Pressure/Pi extension closed: {payload['pressure_pi_extension_closed']}",
        f"Deep action pullback attempt completed: {payload['deep_action_pullback_attempt_completed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Hidden axiom used: {payload['hidden_axiom_used']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rows",
        "",
        "| route | result | closed | selects phi/J/L | meaning |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['route']} | {row['result']} | {row['closed']} | "
            f"{row['selects_phi_j_l']} | {row['meaning']} |"
        )
    lines.extend(["", "## What To Do With This", ""])
    lines.extend(f"- {item}" for item in payload["what_to_do_with_this"])
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
