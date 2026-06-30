from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.vlasov_diagnostic import solve_periodic_poisson_1d
from janus_lab.weakfield_geometry import (
    diagonal_tetrad_1p1,
    metric_from_diagonal_tetrad_1p1,
    periodic_derivative_1d,
    slow_geodesic_acceleration_1d,
    weakfield_b4vol_1p1,
    weakfield_metric_1p1,
)


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_metric_force_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_metric_force_probe.json")


def build_payload() -> dict:
    n = 64
    box = 2.0 * np.pi
    x = np.arange(n) * box / n
    expected_phi = 1e-4 * np.cos(x)
    density = -expected_phi / (4.0 * np.pi)
    phi = solve_periodic_poisson_1d(density, box_size=box, subtract_mean=False)
    psi = np.zeros_like(phi)
    metric = weakfield_metric_1p1(phi, psi)
    tetrad = diagonal_tetrad_1p1(metric)
    reconstructed = metric_from_diagonal_tetrad_1p1(tetrad)
    acceleration = slow_geodesic_acceleration_1d(phi, psi, box)
    minus_grad_phi = -periodic_derivative_1d(phi, box)
    b4vol = weakfield_b4vol_1p1(phi, psi)
    metrics = {
        "max_abs_phi_error": float(np.max(np.abs(phi - expected_phi))),
        "max_abs_metric_reconstruction_error": float(np.max(np.abs(reconstructed - metric))),
        "max_abs_accel_minus_negative_grad_phi": float(np.max(np.abs(acceleration - minus_grad_phi))),
        "min_b4vol_1p1": float(np.min(b4vol)),
        "max_abs_phi": float(np.max(np.abs(phi))),
    }
    return {
        "description": "Diagnostic weak-field Phi/Psi to metric/tetrad/Christoffel force probe.",
        "status": "weakfield-metric-force-probe-diagnostic",
        "depends_on": [
            "p0_janus_metric_tetrad_source_branch_gate",
            "p0_janus_vlasov_geodesic_force_target",
        ],
        "metrics": metrics,
        "metric_reconstructed_from_tetrad": metrics["max_abs_metric_reconstruction_error"] < 1e-12,
        "force_matches_negative_gradient_linear_branch": (
            metrics["max_abs_accel_minus_negative_grad_phi"] < 1e-12
        ),
        "b4vol_1p1_computed": True,
        "source_selected_janus_metric": False,
        "diagnostic_only": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": (
            "This probe verifies the weak-field geometry pipeline on a toy periodic branch. "
            "It does not select the Janus metric/tetrad branch or close B4vol."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Metric Force Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Metric reconstructed from tetrad: {payload['metric_reconstructed_from_tetrad']}",
        "Force matches negative gradient linear branch: "
        f"{payload['force_matches_negative_gradient_linear_branch']}",
        f"B4vol 1+1 computed: {payload['b4vol_1p1_computed']}",
        f"Source-selected Janus metric: {payload['source_selected_janus_metric']}",
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
