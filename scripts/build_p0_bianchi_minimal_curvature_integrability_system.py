from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_same_l_spin_connection_transport_identity_gate import (
    build_payload as build_spin_connection_identity,
)


REPORT_PATH = Path("outputs/reports/p0_bianchi_minimal_curvature_integrability_system.md")
JSON_PATH = Path("outputs/reports/p0_bianchi_minimal_curvature_integrability_system.json")


def build_payload() -> dict:
    spin_connection_identity = build_spin_connection_identity()
    unknowns = [
        {
            "symbol": "A_perp_i",
            "meaning": "transverse boost one-forms not fixed by u^alpha A_alpha=a_req",
            "selected": False,
        },
        {
            "symbol": "R_alpha",
            "meaning": "spatial Lorentz rotations preserving u",
            "selected": False,
        },
        {
            "symbol": "F_relative_alpha_beta",
            "meaning": "F_relative = R_s - L R_o L^{-1} from same-L spin-connection commutator",
            "selected": "source-computable",
        },
    ]
    reduced_equations = [
        {
            "name": "boost_flow_constraint",
            "equation": "u^alpha A_alpha=a_req",
            "role": "already fixed by Bianchi-minimal local flow",
            "closed": True,
        },
        {
            "name": "same_l_curvature_commutator",
            "equation": "[D_alpha,D_beta]L=R_s,alpha_beta L - L R_o,alpha_beta",
            "role": "algebraic integrability identity induced by the same spin-covariant D L",
            "closed": True,
        },
        {
            "name": "relative_curvature_definition",
            "equation": "F_relative_alpha_beta=R_s,alpha_beta - L R_o,alpha_beta L^{-1}",
            "role": "source-computable target once tetrads, spin connections and L are source-derived",
            "closed": True,
        },
        {
            "name": "curvature_match",
            "equation": "D_[alpha Omega_beta]+[Omega_alpha,Omega_beta]=F_relative_alpha_beta",
            "role": "main PDE selecting A_perp_i and R_alpha if a solution exists",
            "closed": False,
        },
        {
            "name": "u_preserving_rotation",
            "equation": "R_alpha_AB u^B=0",
            "role": "keeps spatial rotation invisible to rank-one dust flow but visible to integrability",
            "closed": True,
        },
        {
            "name": "mirror_curvature",
            "equation": "F_relative_mp = inverse-pushforward(F_relative_pm)",
            "role": "prevents plus-only integrability from being promoted",
            "closed": False,
        },
    ]
    outcomes = [
        {
            "case": "pde_has_solution",
            "meaning": "A_perp_i and R_alpha are source-selected by curvature and can define local L",
            "prediction_ready": False,
            "remaining": "mirror residual rows and same-L Q_cross still required",
        },
        {
            "case": "pde_no_solution",
            "meaning": "Bianchi-minimal local branch cannot lift to a full Janus transport",
            "prediction_ready": False,
            "remaining": "reject branch or introduce explicit new axiom",
        },
    ]
    return {
        "description": (
            "Reduced curvature-integrability system for the Bianchi-minimal full connection lift."
        ),
        "status": "curvature-integrability-system-open",
        "depends_on": [
            "p0_bianchi_minimal_full_connection_lift_system",
            "p0_same_l_spin_connection_transport_identity_gate",
        ],
        "unknowns": unknowns,
        "reduced_equations": reduced_equations,
        "outcomes": outcomes,
        "spin_connection_identity_algebra_closed": bool(
            spin_connection_identity["covariant_dl_identity_closed"]
        ),
        "curvature_commutator_identity_closed": True,
        "relative_curvature_formula_closed": True,
        "flow_boost_constraint_closed": True,
        "curvature_match_closed": False,
        "mirror_curvature_closed": False,
        "transverse_unknowns_remain": True,
        "source_computable_not_fitted": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The remaining lift problem is a source-computable PDE: solve transverse boost "
            "A_perp_i and spatial rotation R_alpha so the Lorentz curvature matches the "
            "relative Janus spin-curvature. This is the next real closure test, not a "
            "calibration parameter."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Bianchi-Minimal Curvature Integrability System",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Spin-connection identity algebra closed: {payload['spin_connection_identity_algebra_closed']}",
        f"Curvature commutator identity closed: {payload['curvature_commutator_identity_closed']}",
        f"Relative curvature formula closed: {payload['relative_curvature_formula_closed']}",
        f"Flow boost constraint closed: {payload['flow_boost_constraint_closed']}",
        f"Curvature match closed: {payload['curvature_match_closed']}",
        f"Mirror curvature closed: {payload['mirror_curvature_closed']}",
        f"Transverse unknowns remain: {payload['transverse_unknowns_remain']}",
        f"Source-computable not fitted: {payload['source_computable_not_fitted']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Unknowns",
        "",
        "| symbol | meaning | selected |",
        "|---|---|---|",
    ]
    for row in payload["unknowns"]:
        lines.append(f"| {row['symbol']} | {row['meaning']} | {row['selected']} |")
    lines.extend(["", "## Reduced Equations", "", "| name | equation | role | closed |", "|---|---|---|---|"])
    for row in payload["reduced_equations"]:
        lines.append(f"| {row['name']} | `{row['equation']}` | {row['role']} | {row['closed']} |")
    lines.extend(["", "## Outcomes", "", "| case | meaning | prediction ready | remaining |", "|---|---|---|---|"])
    for row in payload["outcomes"]:
        lines.append(
            f"| {row['case']} | {row['meaning']} | {row['prediction_ready']} | {row['remaining']} |"
        )
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
