from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_dphi_jacobian_volume_identity_target import (
    build_payload as build_jacobian_volume_identity,
)
from scripts.build_p0_same_l_bridge_induces_m_k_qcross_gate import (
    build_payload as build_same_l_stack,
)
from scripts.build_p0_janus_phi_l_xi_map_equation_gate import (
    build_payload as build_xi_map_equation,
)
from scripts.build_p0_source_pullback_metric_response_target import (
    build_payload as build_pullback_response,
)


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_phi_l_map_density_response_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_phi_l_map_density_response_gate.json")


def build_payload() -> dict:
    jacobian = build_jacobian_volume_identity()
    same_l = build_same_l_stack()
    pullback = build_pullback_response()
    xi_gate = build_xi_map_equation()
    response_rows = [
        {
            "name": "scalar_pullback_map_response",
            "formula": "delta_phi(phi^*rho_s)=phi^*(xi^a nabla_a rho_s)",
            "meaning": "map variation of the transported proper scalar density",
            "closed": True,
        },
        {
            "name": "volume_density_map_response",
            "formula": "delta_phi(phi^*(rho_s dmu_s))/dmu_self = B_4vol phi^*(xi^a nabla_a rho_s + rho_s nabla_a xi^a)",
            "meaning": "map variation when the source volume density is transported",
            "closed": True,
        },
        {
            "name": "weakfield_delta_s00_slot",
            "formula": "delta_phi_map_response = phi^*(xi^a nabla_a rho_s) for proper_density_input",
            "meaning": "field residual convention uses proper density plus one explicit B4vol response",
            "closed": True,
        },
        {
            "name": "l_dependence_separation",
            "formula": "delta_L affects velocity/stress projection; delta_phi affects pullback labels/Jacobian",
            "meaning": "do not absorb L response into scalar density transport",
            "closed": True,
        },
    ]
    open_requirements = [
        "derive xi=delta_phi o phi^{-1} from Janus phi/L map equation",
        "prove J_phi/B_4vol identities J1-J4 for the same map branch",
        "prove the same L used for K/Q_cross/Vlasov is compatible with the phi pushforward",
        "mirror the map response for plus_to_minus using phi^{-1}",
        "extend beyond dust before applying to pressure/Pi",
    ]
    return {
        "description": "Weak-field phi/L map-response gate for transported density in delta_S00.",
        "status": "phi-l-map-density-response-algebra-closed-dynamic-selection-open",
        "depends_on": [
            "p0_source_pullback_metric_response_target",
            "p0_dphi_jacobian_volume_identity_target",
            "p0_janus_phi_l_xi_map_equation_gate",
            "p0_same_l_bridge_induces_m_k_qcross_gate",
        ],
        "response_rows": response_rows,
        "open_requirements": open_requirements,
        "scalar_pullback_map_response_closed": True,
        "volume_density_map_response_closed": True,
        "delta_phi_map_response_slot_closed": True,
        "l_density_separation_closed": True,
        "jacobian_volume_identities_closed": bool(jacobian["all_identities_closed"]),
        "same_l_stack_algebra_closed": bool(same_l["same_l_stack_algebra_closed"]),
        "same_l_source_selected": bool(same_l["l_source_selected"]),
        "xi_map_equation_artifact": "p0_janus_phi_l_xi_map_equation_gate",
        "xi_definition_closed": bool(xi_gate["xi_definition_closed"]),
        "xi_solved_from_janus": bool(xi_gate["xi_solved_from_janus"]),
        "mirror_variation_algebra_closed": bool(xi_gate["mirror_variation_algebra_closed"]),
        "pulled_action_bridge_closed": bool(pullback["pulled_action_bridge_closed"]),
        "dynamic_phi_l_selection_closed": False,
        "mirror_map_response_closed": False,
        "full_density_transport_closed": False,
        "pressure_pi_transport_closed": False,
        "uses_observational_fit": False,
        "qdet_absorption_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The local map-response algebra is closed: delta_phi acts by Lie/pullback "
            "on scalar density and source volume density, while delta_L is kept in the "
            "tensor/velocity transport channel. Physical closure still needs the Janus "
            "map equation selecting xi/phi/L, Jacobian-volume identities, mirror response "
            "and non-dust matter transport."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Phi/L Map Density Response Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scalar pullback map response closed: {payload['scalar_pullback_map_response_closed']}",
        f"Volume density map response closed: {payload['volume_density_map_response_closed']}",
        f"Delta phi map response slot closed: {payload['delta_phi_map_response_slot_closed']}",
        f"L density separation closed: {payload['l_density_separation_closed']}",
        f"Jacobian-volume identities closed: {payload['jacobian_volume_identities_closed']}",
        f"Same-L stack algebra closed: {payload['same_l_stack_algebra_closed']}",
        f"Same-L source selected: {payload['same_l_source_selected']}",
        f"Xi map equation artifact: `{payload['xi_map_equation_artifact']}`",
        f"Xi definition closed: {payload['xi_definition_closed']}",
        f"Xi solved from Janus: {payload['xi_solved_from_janus']}",
        f"Mirror variation algebra closed: {payload['mirror_variation_algebra_closed']}",
        f"Pulled action bridge closed: {payload['pulled_action_bridge_closed']}",
        f"Dynamic phi/L selection closed: {payload['dynamic_phi_l_selection_closed']}",
        f"Mirror map response closed: {payload['mirror_map_response_closed']}",
        f"Full density transport closed: {payload['full_density_transport_closed']}",
        f"Pressure/Pi transport closed: {payload['pressure_pi_transport_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Qdet absorption allowed: {payload['qdet_absorption_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Response Rows",
        "",
        "| name | formula | meaning | closed |",
        "|---|---|---|---:|",
    ]
    for row in payload["response_rows"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['meaning']} | {row['closed']} |")
    lines.extend(["", "## Open Requirements", ""])
    lines.extend(f"- {item}" for item in payload["open_requirements"])
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
