from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_relative_strain_q_regular_branch_gate import (
    build_payload as build_q_regular,
)
from scripts.build_p0_bianchi_minimal_full_connection_lift_system import (
    build_payload as build_full_connection,
)
from scripts.build_p0_relative_strain_dh_lgeom_vs_lorentz_gate import (
    build_payload as build_dh_gate,
)


REPORT_PATH = Path("outputs/reports/p0_relative_strain_q_derivative_omega_gate.md")
JSON_PATH = Path("outputs/reports/p0_relative_strain_q_derivative_omega_gate.json")


def divided_difference_log(lambda_i: sp.Symbol, lambda_j: sp.Symbol) -> sp.Expr:
    return sp.simplify((sp.log(lambda_i) - sp.log(lambda_j)) / (lambda_i - lambda_j))


def build_payload() -> dict:
    q_regular = build_q_regular()
    connection = build_full_connection()
    dh_gate = build_dh_gate()
    h, dh = sp.symbols("h dh", positive=True)
    lam_i, lam_j, dh_ij = sp.symbols("lambda_i lambda_j dH_ij", positive=True)
    scalar_dq = sp.diff(sp.log(h) / 2, h) * dh
    offdiag_coeff = sp.simplify(divided_difference_log(lam_i, lam_j) / 2)
    naive_offdiag_coeff = sp.simplify(1 / (2 * lam_i))

    return {
        "description": "Derivative gate for Q=1/2 log(H) tied to the same Omega_alpha transport.",
        "status": "dq-frechet-derivative-gate-open",
        "depends_on": [
            "p0_relative_strain_q_regular_branch_gate",
            "p0_relative_strain_dh_lgeom_vs_lorentz_gate",
            "p0_bianchi_minimal_full_connection_lift_system",
        ],
        "q_definition": q_regular["definition"],
        "same_omega_equation": "D_alpha L_geom=Gamma_alpha L_geom; D_alpha L_Lorentz=Omega_alpha L_Lorentz",
        "dh_source_identity": dh_gate["dh_identity"],
        "dh_source_gate": "p0_relative_strain_dh_lgeom_vs_lorentz_gate",
        "matrix_log_derivative": (
            "D_alpha Q = 1/2 FrechetLog_H[D_alpha H] = "
            "1/2 integral_0^infty (H+sI)^-1 (D_alpha H) (H+sI)^-1 ds"
        ),
        "scalar_commuting_check": {
            "Q(h)": "log(h)/2",
            "D Q": str(scalar_dq),
            "valid_only_if": "[H,D_alpha H]=0 or scalar eigen-branch",
        },
        "eigenbasis_offdiag_check": {
            "frechet_offdiag": str(offdiag_coeff * dh_ij),
            "naive_offdiag": str(naive_offdiag_coeff * dh_ij),
            "naive_equals_frechet_generically": False,
        },
        "same_omega_requirements": [
            "D_alpha H must be computed from the same L/Omega family: the raw L_geom/Gamma branch that induces the L/Omega branch used by K transport",
            "pure eta-antisymmetric Lorentz Omega_alpha alone gives D_alpha H=0 and cannot drive nontrivial Q",
            "DQ must feed A_Janus(Q) with the same Omega_alpha used by Q_cross and Vlasov",
            "do not introduce an independent Q-connection or fitted DQ residual",
            "full Omega_alpha lift must close transverse boosts, rotations, curvature integrability and mirror inverse",
        ],
        "dh_identity_closed": dh_gate["dh_identity_closed"],
        "strain_generator_source_selected": dh_gate["strain_generator_source_selected"],
        "full_omega_alpha_selected": bool(connection["curvature_integrability_closed"]),
        "dq_closed": False,
        "commuting_shortcut_allowed": False,
        "prediction_ready": False,
        "notable_improvement": (
            "The DQ problem is now localized: use the Frechet derivative of the matrix "
            "log on the same regular branch, fed by the eta-symmetric strain part of "
            "D L_geom. The scalar H^{-1}DH shortcut is blocked unless the source "
            "proves a commuting branch."
        ),
        "remaining_lock": (
            "Source-select Gamma_alpha/Sigma_alpha for L_geom, then close the induced "
            "Omega_alpha lift, including curvature integrability and mirror inverse."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Relative Strain Q Derivative Omega Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Q definition: `{payload['q_definition']}`",
        f"Same Omega equation: `{payload['same_omega_equation']}`",
        f"D H source gate: `{payload['dh_source_gate']}`",
        f"D H identity closed: {payload['dh_identity_closed']}",
        f"Strain generator source selected: {payload['strain_generator_source_selected']}",
        f"Full Omega alpha selected: {payload['full_omega_alpha_selected']}",
        f"DQ closed: {payload['dq_closed']}",
        f"Commuting shortcut allowed: {payload['commuting_shortcut_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Matrix Log Derivative",
        "",
        f"`{payload['matrix_log_derivative']}`",
        f"`{payload['dh_source_identity']}`",
        "",
        "## Checks",
        "",
    ]
    for key, value in payload["scalar_commuting_check"].items():
        lines.append(f"- scalar {key}: `{value}`")
    for key, value in payload["eigenbasis_offdiag_check"].items():
        lines.append(f"- eigenbasis {key}: `{value}`")
    lines.extend(["", "## Same-Omega Requirements", ""])
    lines.extend(f"- {item}" for item in payload["same_omega_requirements"])
    lines.extend(["", "## Result", "", payload["notable_improvement"], ""])
    lines.extend([f"Remaining lock: {payload['remaining_lock']}", ""])
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
