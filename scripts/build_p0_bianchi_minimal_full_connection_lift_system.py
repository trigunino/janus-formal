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
from scripts.build_p0_bianchi_minimal_curvature_integrability_system import (
    build_payload as build_curvature_integrability,
)


REPORT_PATH = Path("outputs/reports/p0_bianchi_minimal_full_connection_lift_system.md")
JSON_PATH = Path("outputs/reports/p0_bianchi_minimal_full_connection_lift_system.json")


def build_payload() -> dict:
    spin_connection_identity = build_spin_connection_identity()
    curvature_integrability = build_curvature_integrability()
    decomposition = [
        {
            "piece": "flow_boost",
            "formula": "Omega_u^min = -a_req tensor u_flat + u tensor a_req_flat",
            "selected": True,
            "reason": "fixed by the projected Bianchi force residual",
        },
        {
            "piece": "transverse_boost_one_forms",
            "formula": "A_i with u^alpha A_alpha=a_req and h^alpha_i A_alpha free",
            "selected": False,
            "reason": "Bianchi dust flow fixes only contraction along u",
        },
        {
            "piece": "spatial_rotation_connection",
            "formula": "R_alpha_AB u^B=0, R_alpha_AB=-R_alpha_BA",
            "selected": False,
            "reason": "rank-one dust source is blind to rotations preserving u",
        },
        {
            "piece": "full_connection",
            "formula": "Omega_alpha = -A_alpha tensor u_flat + u tensor A_alpha_flat + R_alpha",
            "selected": False,
            "reason": "requires integrability and mirror constraints",
        },
    ]
    equation_system = [
        "u^alpha A_alpha = a_req",
        "h^alpha_i A_alpha remains unknown until a source/tetrad equation selects it",
        "R_alpha_AB u^B=0",
        "[D_alpha,D_beta]L=R_s,alpha_beta L - L R_o,alpha_beta",
        "F_relative_alpha_beta=R_s,alpha_beta - L R_o,alpha_beta L^{-1}",
        "D_[alpha Omega_beta]+[Omega_alpha,Omega_beta]=F_relative_alpha_beta",
        "D_alpha L=Omega_alpha L with D_alpha L=partial_alpha L+omega_s,alpha L-L omega_o,alpha",
        "L_inverse branch must satisfy the mirror Bianchi residual",
    ]
    acceptance_tests = [
        {
            "test": "local_flow",
            "requires": "Omega_u u = a_req",
            "passed": True,
        },
        {
            "test": "eta_antisymmetry",
            "requires": "Omega_alpha_AB=-Omega_alpha_BA",
            "passed": True,
        },
        {
            "test": "curvature_integrability",
            "requires": "the chosen transverse A_i and R_alpha satisfy the relative curvature equation",
            "passed": False,
        },
        {
            "test": "mirror_inverse",
            "requires": "inverse branch closes the opposite-sector Bianchi row",
            "passed": False,
        },
        {
            "test": "same_l_qcross",
            "requires": "Q_cross consumes the same L solved by D_alpha L=Omega_alpha L",
            "passed": False,
        },
    ]
    return {
        "description": "Equation system for lifting the Bianchi-minimal local Omega_u solution to a full Omega_alpha.",
        "status": "full-connection-lift-system-open",
        "depends_on": [
            "p0_bianchi_minimal_joint_dl_dlogb_solution",
            "p0_bianchi_minimal_integrability_mirror_gate",
            "p0_same_l_spin_connection_transport_identity_gate",
            "p0_bianchi_minimal_curvature_integrability_system",
        ],
        "decomposition": decomposition,
        "equation_system": equation_system,
        "acceptance_tests": acceptance_tests,
        "local_flow_closed": True,
        "eta_antisymmetry_closed": True,
        "spin_connection_identity_algebra_closed": bool(
            spin_connection_identity["covariant_dl_identity_closed"]
        ),
        "spin_connection_identity_source_selected": bool(spin_connection_identity["source_selected_l"]),
        "curvature_commutator_identity_closed": bool(
            curvature_integrability["curvature_commutator_identity_closed"]
        ),
        "relative_curvature_formula_closed": bool(
            curvature_integrability["relative_curvature_formula_closed"]
        ),
        "transverse_boost_selected": False,
        "spatial_rotation_selected": False,
        "curvature_integrability_closed": False,
        "mirror_inverse_closed": False,
        "same_l_qcross_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The local Bianchi branch determines the flow boost only. A full connection "
            "requires transverse boost one-forms and spatial rotations satisfying curvature "
            "integrability, mirror inverse closure, and same-L Q_cross. These are equations, "
            "not fitted knobs."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Bianchi-Minimal Full Connection Lift System",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Local flow closed: {payload['local_flow_closed']}",
        f"Eta antisymmetry closed: {payload['eta_antisymmetry_closed']}",
        f"Spin-connection identity algebra closed: {payload['spin_connection_identity_algebra_closed']}",
        f"Spin-connection identity source selected: {payload['spin_connection_identity_source_selected']}",
        f"Curvature commutator identity closed: {payload['curvature_commutator_identity_closed']}",
        f"Relative curvature formula closed: {payload['relative_curvature_formula_closed']}",
        f"Transverse boost selected: {payload['transverse_boost_selected']}",
        f"Spatial rotation selected: {payload['spatial_rotation_selected']}",
        f"Curvature integrability closed: {payload['curvature_integrability_closed']}",
        f"Mirror inverse closed: {payload['mirror_inverse_closed']}",
        f"Same L Q_cross closed: {payload['same_l_qcross_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Decomposition",
        "",
        "| piece | formula | selected | reason |",
        "|---|---|---|---|",
    ]
    for row in payload["decomposition"]:
        lines.append(f"| {row['piece']} | `{row['formula']}` | {row['selected']} | {row['reason']} |")
    lines.extend(["", "## Equation System", ""])
    lines.extend(f"- `{item}`" for item in payload["equation_system"])
    lines.extend(["", "## Acceptance Tests", "", "| test | requires | passed |", "|---|---|---|"])
    for row in payload["acceptance_tests"]:
        lines.append(f"| {row['test']} | {row['requires']} | {row['passed']} |")
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
