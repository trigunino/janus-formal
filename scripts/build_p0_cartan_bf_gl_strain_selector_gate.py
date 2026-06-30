from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_action_ghost_stability_gate import build_payload as build_ghost_gate
from scripts.build_p0_bf_connection_constraint_route import build_payload as build_bf_route
from scripts.build_p0_bianchi_minimal_curvature_integrability_system import (
    build_payload as build_integrability,
)
from scripts.build_p0_bianchi_minimal_same_l_qcross_gate import (
    build_payload as build_same_l_qcross,
)
from scripts.build_p0_sigma_dh_equivalence_gate import build_payload as build_sigma_gate


REPORT_PATH = Path("outputs/reports/p0_cartan_bf_gl_strain_selector_gate.md")
JSON_PATH = Path("outputs/reports/p0_cartan_bf_gl_strain_selector_gate.json")


def build_payload() -> dict:
    bf = build_bf_route()
    sigma = build_sigma_gate()
    ghost = build_ghost_gate()
    integrability = build_integrability()
    same_l = build_same_l_qcross()
    return {
        "description": "Gate for extending the BF/Cartan connection route to a GL strain sector selecting Sigma_alpha/D_alpha H.",
        "status": "cartan-bf-gl-strain-selector-open",
        "depends_on": [
            "p0_bf_connection_constraint_route",
            "p0_sigma_dh_equivalence_gate",
            "p0_action_ghost_stability_gate",
            "p0_bianchi_minimal_curvature_integrability_system",
            "p0_bianchi_minimal_same_l_qcross_gate",
        ],
        "connection_decomposition": [
            "Gamma_alpha = Omega_alpha + Sigma_alpha",
            "Omega_alpha^dagger_eta=-Omega_alpha",
            "Sigma_alpha^dagger_eta=Sigma_alpha",
            "D_alpha H = 2 eta^{-1} L_geom^T eta Sigma_alpha L_geom",
        ],
        "bf_route_status": bf["status"],
        "sigma_equivalence_status": sigma["status"],
        "ghost_gate_status": ghost["status"],
        "integrability_status": integrability["status"],
        "same_l_qcross_status": same_l["status"],
        "required_source_terms": [
            "Phi_R[source Janus] for antisymmetric Lorentz curvature",
            "Phi_Sigma[source Janus] or N_alpha[source Janus] for symmetric strain/nonmetricity",
            "same L_geom/L_Lorentz relation used by K, Q_cross, optics and Vlasov",
        ],
        "rejection_rules": [
            "do not insert Phi_Sigma or N_alpha target by hand",
            "do not let BF multipliers impose residual cancellation as a post-hoc constraint",
            "do not accept symmetric GL kinetic terms before ghost/stability screening",
            "do not split K transport and Q_cross onto different L branches",
        ],
        "selects_sigma_dh": False,
        "selects_sigma_dh_conditionally": True,
        "new_axiom_risk": True,
        "integrability_required": True,
        "ghost_gate_required": True,
        "same_l_qcross_required": True,
        "source_phi_sigma_found": False,
        "prediction_ready": False,
        "notable_improvement": (
            "The BF route now has a concrete GL extension target: source-select the "
            "symmetric strain curvature/nonmetricity sector, not just Lorentz curvature."
        ),
        "remaining_lock": (
            "Derive Phi_Sigma/N_alpha from Janus source equations and pass integrability, "
            "same-L and ghost gates."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Cartan BF GL Strain Selector Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Selects Sigma/DH: {payload['selects_sigma_dh']}",
        f"Selects Sigma/DH conditionally: {payload['selects_sigma_dh_conditionally']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"Integrability required: {payload['integrability_required']}",
        f"Ghost gate required: {payload['ghost_gate_required']}",
        f"Same-L Q_cross required: {payload['same_l_qcross_required']}",
        f"Source Phi_Sigma found: {payload['source_phi_sigma_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Connection Decomposition",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["connection_decomposition"])
    lines.extend(["", "## Required Source Terms", ""])
    lines.extend(f"- {item}" for item in payload["required_source_terms"])
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
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
