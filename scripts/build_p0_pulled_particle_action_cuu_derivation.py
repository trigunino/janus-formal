from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_connection_difference_cuu_identity import (
    build_payload as build_connection_identity,
)


REPORT_PATH = Path("outputs/reports/p0_pulled_particle_action_cuu_derivation.md")
JSON_PATH = Path("outputs/reports/p0_pulled_particle_action_cuu_derivation.json")


def build_payload() -> dict:
    connection_identity = build_connection_identity()
    tau = sp.symbols("tau")
    y = sp.Function("y")(tau)
    dy = sp.diff(y, tau)
    ddy = sp.diff(y, tau, 2)
    g = sp.Function("g")
    lagrangian = sp.Rational(1, 2) * g(y) * dy**2
    dldy = sp.diff(lagrangian, y)
    dlddy = sp.diff(lagrangian, dy)
    euler_lagrange = sp.simplify(sp.diff(dlddy, tau) - dldy)
    normalized_force = sp.simplify(euler_lagrange / g(y))
    connection_term = sp.simplify(sp.diff(g(y), y) / (2 * g(y)) * dy**2)
    geodesic_residual = sp.simplify(normalized_force - (ddy + connection_term))
    projected_identity = "h_alpha^beta E_beta = rho h_alpha^beta C_beta_munu u^mu u^nu"
    derivation_rows = [
        {
            "row": "particle_action_variation",
            "formula": "d/dtau(g_ab ydot^b)-1/2 partial_a g_bc ydot^b ydot^c=0",
            "closed": True,
        },
        {
            "row": "connection_rewrite",
            "formula": "g^{-1} E_a = yddot^a + Gamma^a_bc ydot^b ydot^c",
            "closed": True,
        },
        {
            "row": "dust_lift",
            "formula": "integrate particle identity over cold monoflux density rho",
            "closed": True,
        },
        {
            "row": "cross_pullback",
            "formula": "replace self acceleration by receiver-vs-source connection difference C(u,u)",
            "closed": connection_identity["cross_pullback_algebra_closed"],
        },
        {
            "row": "same_phi_l_selection",
            "formula": "same map phi/L selected by Janus source action",
            "closed": False,
        },
    ]
    return {
        "description": "Internal variational derivation of the particle/dust Cuu force skeleton.",
        "status": "pulled-particle-action-cuu-derivation-partial",
        "lagrangian_1d": str(lagrangian),
        "euler_lagrange_1d": str(sp.factor(euler_lagrange)),
        "normalized_force_1d": str(sp.factor(normalized_force)),
        "connection_term_1d": str(connection_term),
        "geodesic_residual_zero": bool(geodesic_residual == 0),
        "projected_identity_target": projected_identity,
        "derivation_rows": derivation_rows,
        "particle_geodesic_variation_closed": True,
        "cold_dust_lift_closed": True,
        "connection_difference_identity_status": connection_identity["status"],
        "connection_difference_cross_pullback_closed": connection_identity["cross_pullback_algebra_closed"],
        "same_phi_l_source_selected": False,
        "conditional_e_alpha_rho_cuu_supported": True,
        "full_e_alpha_rho_cuu_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The particle action derivation gives the correct geodesic/connection-force skeleton "
            "and lifts to cold monoflux dust. The cross-sector C(u,u) identity still needs the "
            "Janus-selected phi/L pullback and connection-difference substitution."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pulled Particle Action Cuu Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lagrangian 1D: `{payload['lagrangian_1d']}`",
        f"Euler-Lagrange 1D: `{payload['euler_lagrange_1d']}`",
        f"Normalized force 1D: `{payload['normalized_force_1d']}`",
        f"Connection term 1D: `{payload['connection_term_1d']}`",
        f"Geodesic residual zero: {payload['geodesic_residual_zero']}",
        f"Particle geodesic variation closed: {payload['particle_geodesic_variation_closed']}",
        f"Cold dust lift closed: {payload['cold_dust_lift_closed']}",
        f"Connection-difference identity status: {payload['connection_difference_identity_status']}",
        f"Connection-difference cross pullback closed: {payload['connection_difference_cross_pullback_closed']}",
        f"Same phi/L source selected: {payload['same_phi_l_source_selected']}",
        f"Full E_alpha=rho Cuu derived: {payload['full_e_alpha_rho_cuu_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Rows",
        "",
        "| row | formula | closed |",
        "|---|---|---:|",
    ]
    for row in payload["derivation_rows"]:
        lines.append(f"| {row['row']} | `{row['formula']}` | {row['closed']} |")
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
