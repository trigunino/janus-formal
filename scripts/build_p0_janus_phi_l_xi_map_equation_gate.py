from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_janus_phi_l_ephi_el_variational_origin_gate import (
    build_payload as build_ephi_el_origin,
)


REPORT_PATH = Path("outputs/reports/p0_janus_phi_l_xi_map_equation_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_phi_l_xi_map_equation_gate.json")


def build_payload() -> dict:
    ephi_el = build_ephi_el_origin()
    variation_rows = [
        {
            "name": "xi_definition",
            "formula": "xi^a = delta_phi^a o phi^{-1}",
            "meaning": "Eulerian source-side generator of the map variation",
            "closed": True,
        },
        {
            "name": "pullback_variation",
            "formula": "delta_phi(phi^*A)=phi^*(Lie_xi A)",
            "meaning": "all scalar, tensor and volume pullback responses use the same xi",
            "closed": True,
        },
        {
            "name": "inverse_map_variation",
            "formula": "delta(phi^{-1}) = - (phi^{-1})_* xi",
            "meaning": "mirror map response is fixed by the inverse constraint",
            "closed": True,
        },
        {
            "name": "l_generator",
            "formula": "Lambda = delta L L^{-1}; delta(L^{-1})=-L^{-1} delta L L^{-1}",
            "meaning": "tetrad bridge variation has an inverse mirror generator",
            "closed": True,
        },
        {
            "name": "formal_map_el",
            "formula": "delta S = int(E_phi_a xi^a + E_L_AB Lambda^{AB}) dmu",
            "meaning": "Janus must provide E_phi=0 and E_L=0 before xi/Lambda are solved",
            "closed": True,
        },
    ]
    open_requirements = [
        "supply a Janus source/action equation for E_phi_a",
        "supply a Janus source/action equation for E_L_AB",
        "prove boundary/gauge conditions make the map equation invertible",
        "reuse the same xi/Lambda branch in density, Cuu, K, Q_cross and Vlasov transport",
        "reject observational residual tuning as a replacement for E_phi/E_L",
    ]
    return {
        "description": "P0 gate for the xi=delta_phi o phi^{-1} map-equation variable and mirror algebra.",
        "status": "xi-map-variation-algebra-closed-source-equation-open",
        "variation_rows": variation_rows,
        "open_requirements": open_requirements,
        "ephi_el_origin_artifact": "p0_janus_phi_l_ephi_el_variational_origin_gate",
        "xi_definition_closed": True,
        "pullback_variation_closed": True,
        "inverse_map_variation_closed": True,
        "l_inverse_variation_closed": True,
        "formal_map_el_written": True,
        "e_phi_candidate_written": bool(ephi_el["e_phi_candidate_written"]),
        "e_l_candidate_written": bool(ephi_el["e_l_candidate_written"]),
        "source_coupled_action_required": bool(ephi_el["source_coupled_action_required"]),
        "published_janus_e_phi_supplied": bool(ephi_el["published_janus_e_phi_supplied"]),
        "published_janus_e_l_supplied": bool(ephi_el["published_janus_e_l_supplied"]),
        "janus_e_phi_supplied": False,
        "janus_e_l_supplied": False,
        "xi_solved_from_janus": False,
        "lambda_solved_from_janus": False,
        "dynamic_phi_l_selection_closed": False,
        "mirror_variation_algebra_closed": True,
        "uses_observational_fit": False,
        "hidden_axiom_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Yes: the correct xi/Lambda variation variables and mirror laws are closed. "
            "No physical xi is selected until Janus supplies E_phi and E_L equations "
            "or an accepted action."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Phi/L Xi Map Equation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Xi definition closed: {payload['xi_definition_closed']}",
        f"Pullback variation closed: {payload['pullback_variation_closed']}",
        f"Inverse map variation closed: {payload['inverse_map_variation_closed']}",
        f"L inverse variation closed: {payload['l_inverse_variation_closed']}",
        f"Formal map EL written: {payload['formal_map_el_written']}",
        f"E_phi/E_L origin artifact: `{payload['ephi_el_origin_artifact']}`",
        f"E_phi candidate written: {payload['e_phi_candidate_written']}",
        f"E_L candidate written: {payload['e_l_candidate_written']}",
        f"Source-coupled action required: {payload['source_coupled_action_required']}",
        f"Published Janus E_phi supplied: {payload['published_janus_e_phi_supplied']}",
        f"Published Janus E_L supplied: {payload['published_janus_e_l_supplied']}",
        f"Janus E_phi supplied: {payload['janus_e_phi_supplied']}",
        f"Janus E_L supplied: {payload['janus_e_l_supplied']}",
        f"Xi solved from Janus: {payload['xi_solved_from_janus']}",
        f"Dynamic phi/L selection closed: {payload['dynamic_phi_l_selection_closed']}",
        f"Mirror variation algebra closed: {payload['mirror_variation_algebra_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Variation Rows",
        "",
        "| name | formula | meaning | closed |",
        "|---|---|---|---:|",
    ]
    for row in payload["variation_rows"]:
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
