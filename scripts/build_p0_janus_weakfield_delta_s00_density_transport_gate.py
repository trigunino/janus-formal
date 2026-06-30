from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_dust_pullback_density_response_bridge import (
    build_payload as build_density_response_bridge,
)
from scripts.build_p0_effective_density_continuity_pullback_proof import (
    build_payload as build_effective_density_continuity,
)
from scripts.build_p0_janus_weakfield_delta_s00_measure_convention_gate import (
    build_payload as build_measure_convention,
)
from scripts.build_p0_janus_weakfield_phi_l_map_density_response_gate import (
    build_payload as build_phi_l_map_response,
)


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_delta_s00_density_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_delta_s00_density_transport_gate.json")


def build_payload() -> dict:
    continuity = build_effective_density_continuity()
    response = build_density_response_bridge()
    measure = build_measure_convention()
    phi_l_response = build_phi_l_map_response()
    transport_rows = [
        {
            "name": "proper_density_transport_slot",
            "formula": "delta_rho_other_to_self = phi^*(delta_rho_other) + delta_phi_map_response",
            "status": "slot-written-map-response-open",
        },
        {
            "name": "effective_current_continuity",
            "formula": "D_self(B_4vol rho_other_to_self u_other_to_self)=0",
            "status": "closed-for-single-cross-dust-pullback",
        },
        {
            "name": "effective_density_response",
            "formula": "delta rho_eff = delta_rho_other_to_self + rho0_other_to_self delta_B_4vol",
            "status": "closed-chain-rule",
        },
        {
            "name": "delta_s00_input_rule",
            "formula": "field residual uses proper_density_input; do not feed rho_eff and B_4vol together",
            "status": "condition-selected-no-double-counting",
        },
    ]
    open_requirements = [
        "derive delta_phi_map_response from the same Janus phi/L branch",
        "prove mirror plus/minus density transport with the inverse map",
        "close source pullback metric response of rho_to before varying the full action",
        "keep pressure/Pi outside this dust-density transport gate",
    ]
    return {
        "description": "Weak-field delta_S00 gate for transported cross-dust density slots.",
        "status": "delta-s00-density-transport-slot-written-physics-open",
        "depends_on": [
            "p0_effective_density_continuity_pullback_proof",
            "p0_dust_pullback_density_response_bridge",
            "p0_janus_weakfield_delta_s00_measure_convention_gate",
            "p0_janus_weakfield_phi_l_map_density_response_gate",
        ],
        "transport_rows": transport_rows,
        "open_requirements": open_requirements,
        "field_residual_convention_selected": bool(measure["field_residual_convention_selected"]),
        "selected_field_residual_convention": measure["selected_field_residual_convention"],
        "single_cross_dust_effective_continuity_closed": bool(
            continuity["single_cross_dust_effective_continuity_closed"]
        ),
        "density_response_chain_rule_closed": bool(response["density_response_chain_rule_closed"]),
        "receiver_measure_response_closed": bool(response["receiver_measure_response_closed"]),
        "source_pullback_metric_response_closed": bool(
            response["source_pullback_metric_response_closed"]
        ),
        "phi_l_map_response_artifact": "p0_janus_weakfield_phi_l_map_density_response_gate",
        "delta_phi_map_response_slot_closed": bool(
            phi_l_response["delta_phi_map_response_slot_closed"]
        ),
        "dynamic_phi_l_selection_closed": bool(
            phi_l_response["dynamic_phi_l_selection_closed"]
        ),
        "mirror_map_response_closed": bool(phi_l_response["mirror_map_response_closed"]),
        "weakfield_density_transport_slot_written": True,
        "full_density_transport_closed": False,
        "pressure_pi_transport_closed": False,
        "uses_observational_fit": False,
        "qdet_absorption_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The delta_S00 transported-density slot is now explicit and compatible "
            "with the single-cross dust pullback continuity identity. Full closure "
            "still needs the Janus phi/L map response, mirror transport and source "
            "metric response."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Delta S00 Density Transport Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Field residual convention selected: {payload['field_residual_convention_selected']}",
        f"Selected field residual convention: `{payload['selected_field_residual_convention']}`",
        f"Single cross dust effective continuity closed: {payload['single_cross_dust_effective_continuity_closed']}",
        f"Density response chain rule closed: {payload['density_response_chain_rule_closed']}",
        f"Receiver measure response closed: {payload['receiver_measure_response_closed']}",
        f"Source pullback metric response closed: {payload['source_pullback_metric_response_closed']}",
        f"Phi/L map response artifact: `{payload['phi_l_map_response_artifact']}`",
        f"Delta phi map response slot closed: {payload['delta_phi_map_response_slot_closed']}",
        f"Dynamic phi/L selection closed: {payload['dynamic_phi_l_selection_closed']}",
        f"Mirror map response closed: {payload['mirror_map_response_closed']}",
        f"Weakfield density transport slot written: {payload['weakfield_density_transport_slot_written']}",
        f"Full density transport closed: {payload['full_density_transport_closed']}",
        f"Pressure/Pi transport closed: {payload['pressure_pi_transport_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Qdet absorption allowed: {payload['qdet_absorption_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Transport Rows",
        "",
        "| name | formula | status |",
        "|---|---|---|",
    ]
    for row in payload["transport_rows"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['status']} |")
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
