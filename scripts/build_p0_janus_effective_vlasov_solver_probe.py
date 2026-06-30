from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.vlasov_diagnostic import (
    gaussian_phase_space,
    strang_step_periodic,
    total_mass,
    velocity_moments,
)


REPORT_PATH = Path("outputs/reports/p0_janus_effective_vlasov_solver_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_effective_vlasov_solver_probe.json")


def build_payload() -> dict:
    nx = 32
    nv = 32
    box_size = 1.0
    x = (np.arange(nx) + 0.5) * box_size / nx
    v = np.linspace(-1.0, 1.0, nv, endpoint=False)
    dx = box_size / nx
    dv = v[1] - v[0]
    f0 = gaussian_phase_space(x, v, x0=0.35, sigma_x=0.07, sigma_v=0.22, box_size=box_size)
    acceleration = 0.05 * np.sin(2.0 * np.pi * x)
    f1 = strang_step_periodic(f0, v, acceleration, dt=0.01, dx=dx, dv=dv)
    m0 = velocity_moments(f0, v, dv)
    m1 = velocity_moments(f1, v, dv)
    metrics = {
        "mass_initial": total_mass(f0, dx, dv),
        "mass_final": total_mass(f1, dx, dv),
        "mass_abs_error": abs(total_mass(f1, dx, dv) - total_mass(f0, dx, dv)),
        "min_f_final": float(np.min(f1)),
        "max_abs_delta_rho": float(np.max(np.abs(m1["rho"] - m0["rho"]))),
        "max_abs_q_final": float(np.max(np.abs(m1["Q"]))),
    }
    return {
        "description": "Diagnostic 1D-1V periodic Vlasov solver probe for moment extraction only.",
        "status": "effective-vlasov-solver-probe-diagnostic",
        "depends_on": [
            "p0_janus_effective_vlasov_solver_gate",
            "p0_janus_full_vlasov_moment_closure_contract",
        ],
        "grid": {"nx": nx, "nv": nv, "box_size": box_size},
        "metrics": metrics,
        "moment_fields": ["rho", "beta", "P", "p", "Pi", "Q"],
        "diagnostic_only": True,
        "uses_toy_force": True,
        "uses_source_derived_janus_force": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": (
            "Periodic 1D-1V diagnostic only. This is not a source-derived Janus Vlasov solver, "
            "not a calibrated cosmological simulation, and not a prediction layer."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Effective Vlasov Solver Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Diagnostic only: {payload['diagnostic_only']}",
        f"Uses toy force: {payload['uses_toy_force']}",
        f"Uses source-derived Janus force: {payload['uses_source_derived_janus_force']}",
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
    lines.extend(
        [
            "",
            f"Moment fields: `{', '.join(payload['moment_fields'])}`",
            "",
            f"Boundary: {payload['boundary']}",
            "",
        ]
    )
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
