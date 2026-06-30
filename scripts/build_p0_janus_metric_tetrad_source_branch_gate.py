from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_metric_tetrad_source_branch_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_metric_tetrad_source_branch_gate.json")


def build_payload() -> dict:
    branch_steps = [
        "select plus/minus metric branch from Janus field/source equations",
        "derive tetrads e_plus and e_minus from those metrics",
        "compute spin connections omega_plus and omega_minus",
        "compute Christoffel symbols Gamma_plus and Gamma_minus",
        "feed Gamma into geodesics, Vlasov force, same-L transport, and Weyl/shear chain",
    ]
    acceptance = [
        "metric equations use published/source-traced Janus signs and density conventions",
        "tetrads reproduce their metrics: g_AB=eta_ab e^a_A e^b_B",
        "spin connections are compatible with tetrads and torsion convention",
        "same branch supplies G0i, Q_det, B_4vol, and Vlasov force",
        "no observational normalization selects the branch",
    ]
    open_items = [
        "source-selected perturbed metric branch",
        "unique gauge/lapse/slice convention",
        "cross-sector tetrad relation used by L_minus_to_plus",
        "boundary/background mode selection",
    ]
    return {
        "description": "P0 gate for deriving the Janus metric/tetrad branch before Vlasov or same-L claims.",
        "status": "metric-tetrad-source-branch-gate-open",
        "depends_on": [
            "p0_janus_weakfield_source_potential_system",
            "p0_janus_source_tetrad_requirements",
            "p0_janus_weakfield_metric_tetrad_bridge",
        ],
        "branch_steps": branch_steps,
        "acceptance": acceptance,
        "open_items": open_items,
        "metric_branch_steps_written": True,
        "tetrad_reconstruction_required": True,
        "spin_connection_required": True,
        "christoffel_required_for_vlasov": True,
        "weakfield_metric_force_probe_available": True,
        "source_selected_metric_branch_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The metric/tetrad branch must be selected before A_Janus, same-L, Q_det/B_4vol, "
            "or Weyl/shear can be promoted. This gate records the required source chain; it "
            "does not close the branch."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Metric/Tetrad Source Branch Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Metric branch steps written: {payload['metric_branch_steps_written']}",
        f"Tetrad reconstruction required: {payload['tetrad_reconstruction_required']}",
        f"Spin connection required: {payload['spin_connection_required']}",
        f"Christoffel required for Vlasov: {payload['christoffel_required_for_vlasov']}",
        f"Weak-field metric force probe available: {payload['weakfield_metric_force_probe_available']}",
        f"Source-selected metric branch closed: {payload['source_selected_metric_branch_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Branch Steps",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["branch_steps"])
    lines.extend(["", "## Acceptance", ""])
    lines.extend(f"- {item}" for item in payload["acceptance"])
    lines.extend(["", "## Open Items", ""])
    lines.extend(f"- {item}" for item in payload["open_items"])
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
