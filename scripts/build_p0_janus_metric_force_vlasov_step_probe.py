from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.vlasov_diagnostic import gaussian_phase_space, strang_step_periodic, total_mass, velocity_moments
from janus_lab.weakfield_geometry import slow_geodesic_acceleration_1d, weakfield_b4vol_1p1


REPORT_PATH = Path("outputs/reports/p0_janus_metric_force_vlasov_step_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_metric_force_vlasov_step_probe.json")


def build_payload() -> dict:
    nx = 64
    nv = 32
    box = 2.0 * np.pi
    x = np.arange(nx) * box / nx
    v = np.linspace(-1.0, 1.0, nv, endpoint=False)
    dx = box / nx
    dv = v[1] - v[0]
    phi = 1e-4 * np.cos(x)
    psi = np.zeros_like(phi)
    acceleration = slow_geodesic_acceleration_1d(phi, psi, box)
    f0 = gaussian_phase_space(x, v, x0=np.pi, sigma_x=0.35, sigma_v=0.25, box_size=box)
    f1 = strang_step_periodic(f0, v, acceleration, dt=0.01, dx=dx, dv=dv)
    moments = velocity_moments(f1, v, dv)
    b4vol = weakfield_b4vol_1p1(phi, psi)
    metrics = {
        "mass_error": abs(total_mass(f1, dx, dv) - total_mass(f0, dx, dv)),
        "min_f_final": float(np.min(f1)),
        "max_abs_acceleration": float(np.max(np.abs(acceleration))),
        "max_abs_q_final": float(np.max(np.abs(moments["Q"]))),
        "min_b4vol_1p1": float(np.min(b4vol)),
    }
    return {
        "description": "Diagnostic Vlasov step driven by weak-field metric geodesic force.",
        "status": "metric-force-vlasov-step-probe-diagnostic",
        "depends_on": [
            "p0_janus_weakfield_metric_force_probe",
            "p0_janus_effective_vlasov_solver_probe",
        ],
        "metrics": metrics,
        "uses_metric_geodesic_force": True,
        "uses_source_selected_janus_metric": False,
        "uses_same_l_transport": False,
        "diagnostic_only": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": (
            "This links the diagnostic weak-field metric force to one Vlasov step. "
            "It is not a source-selected Janus phase-space transport law."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Metric-Force Vlasov Step Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Uses metric geodesic force: {payload['uses_metric_geodesic_force']}",
        f"Uses source-selected Janus metric: {payload['uses_source_selected_janus_metric']}",
        f"Uses same-L transport: {payload['uses_same_l_transport']}",
        f"Diagnostic only: {payload['diagnostic_only']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Metrics",
        "",
        "| metric | value |",
        "|---|---:|",
    ]
    for name, value in payload["metrics"].items():
        lines.append(f"| {name} | {value:.6g} |")
    lines.extend(["", f"Boundary: {payload['boundary']}", ""])
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
