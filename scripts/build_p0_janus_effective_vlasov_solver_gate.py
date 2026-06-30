from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_effective_vlasov_solver_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_effective_vlasov_solver_gate.json")


def build_payload() -> dict:
    solver_layers = [
        "diagnostic 1D/2D phase-space advection kernel for f",
        "source-derived force plugin A_Janus from metric connection",
        "moment extractor for rho, beta_i, P_ij, p, Pi_ij, Q_ijk",
        "same-L projection layer for cross-sector moments",
        "mass/positivity/convergence diagnostics before any observable layer",
    ]
    required_inputs = [
        "metric/tetrad source branch",
        "same-L transport stack",
        "phase-space B_4vol/dP measure convention",
        "Janus initial distribution f_plus/f_minus",
        "boundary and zero-mode policy",
    ]
    allowed_outputs_now = [
        "diagnostic solver interface",
        "moment-conservation tests",
        "toy force regression tests",
        "no prediction and no survey comparison",
    ]
    return {
        "description": "P0 gate for an effective Janus Vlasov solver without claiming physical closure.",
        "status": "effective-vlasov-solver-gate-open",
        "depends_on": [
            "p0_janus_vlasov_geodesic_force_target",
            "p0_janus_phase_space_b4vol_measure_gate",
            "p0_janus_same_l_transport_stack_gate",
        ],
        "solver_layers": solver_layers,
        "required_inputs": required_inputs,
        "allowed_outputs_now": allowed_outputs_now,
        "solver_interface_defined": True,
        "diagnostic_solver_probe_available": True,
        "two_sector_vlasov_poisson_probe_available": True,
        "metric_force_vlasov_step_probe_available": True,
        "two_sector_metric_force_vlasov_probe_available": True,
        "source_force_plugin_required": True,
        "moment_extractor_required": True,
        "diagnostic_only": True,
        "effective_vlasov_solver_physics_ready": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The solver can be built as a diagnostic kernel now, but it becomes physical only "
            "after metric/tetrad, same-L, measure, and initial distribution gates close."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Effective Vlasov Solver Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Solver interface defined: {payload['solver_interface_defined']}",
        f"Diagnostic solver probe available: {payload['diagnostic_solver_probe_available']}",
        "Two-sector Vlasov-Poisson probe available: "
        f"{payload['two_sector_vlasov_poisson_probe_available']}",
        "Metric-force Vlasov step probe available: "
        f"{payload['metric_force_vlasov_step_probe_available']}",
        "Two-sector metric-force Vlasov probe available: "
        f"{payload['two_sector_metric_force_vlasov_probe_available']}",
        f"Source force plugin required: {payload['source_force_plugin_required']}",
        f"Moment extractor required: {payload['moment_extractor_required']}",
        f"Diagnostic only: {payload['diagnostic_only']}",
        f"Effective Vlasov solver physics ready: {payload['effective_vlasov_solver_physics_ready']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Solver Layers",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["solver_layers"])
    lines.extend(["", "## Required Inputs", ""])
    lines.extend(f"- {item}" for item in payload["required_inputs"])
    lines.extend(["", "## Allowed Outputs Now", ""])
    lines.extend(f"- {item}" for item in payload["allowed_outputs_now"])
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
