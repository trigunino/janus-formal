from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.vlasov_diagnostic import (
    gaussian_phase_space,
    strang_step_periodic,
    total_mass,
    two_sector_vlasov_poisson_accelerations,
    velocity_moments,
)


REPORT_PATH = Path("outputs/reports/p0_janus_two_sector_vlasov_poisson_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_two_sector_vlasov_poisson_probe.json")


def build_payload() -> dict:
    nx = 32
    nv = 32
    box_size = 1.0
    x = (np.arange(nx) + 0.5) * box_size / nx
    v = np.linspace(-1.0, 1.0, nv, endpoint=False)
    dx = box_size / nx
    dv = v[1] - v[0]
    f_plus = gaussian_phase_space(x, v, x0=0.32, sigma_x=0.07, sigma_v=0.22, box_size=box_size)
    f_minus = gaussian_phase_space(x, v, x0=0.68, sigma_x=0.07, sigma_v=0.22, box_size=box_size)
    a_plus, a_minus, rho_eff = two_sector_vlasov_poisson_accelerations(
        f_plus,
        f_minus,
        v,
        dv,
        box_size=box_size,
    )
    plus_next = strang_step_periodic(f_plus, v, a_plus, dt=0.005, dx=dx, dv=dv)
    minus_next = strang_step_periodic(f_minus, v, a_minus, dt=0.005, dx=dx, dv=dv)
    plus_moments = velocity_moments(plus_next, v, dv)
    metrics = {
        "mass_plus_error": abs(total_mass(plus_next, dx, dv) - total_mass(f_plus, dx, dv)),
        "mass_minus_error": abs(total_mass(minus_next, dx, dv) - total_mass(f_minus, dx, dv)),
        "max_abs_a_plus_plus_a_minus": float(np.max(np.abs(a_plus + a_minus))),
        "mean_effective_density": float(np.mean(rho_eff)),
        "min_f_plus_next": float(np.min(plus_next)),
        "max_abs_q_plus_next": float(np.max(np.abs(plus_moments["Q"]))),
    }
    return {
        "description": "Diagnostic two-sector 1D-1V Vlasov-Poisson probe.",
        "status": "two-sector-vlasov-poisson-probe-diagnostic",
        "depends_on": [
            "p0_janus_effective_vlasov_solver_probe",
            "p0_janus_effective_vlasov_solver_gate",
        ],
        "grid": {"nx": nx, "nv": nv, "box_size": box_size},
        "metrics": metrics,
        "uses_periodic_poisson": True,
        "sector_accelerations_conjugate": metrics["max_abs_a_plus_plus_a_minus"] < 1e-12,
        "diagnostic_only": True,
        "uses_source_derived_metric_branch": False,
        "uses_same_l_transport": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": (
            "Periodic 1D-1V Vlasov-Poisson diagnostic only. It does not close Janus metric/tetrad, "
            "same-L, B4vol/dP, or cosmological prediction gates."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Two-Sector Vlasov-Poisson Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Uses periodic Poisson: {payload['uses_periodic_poisson']}",
        f"Sector accelerations conjugate: {payload['sector_accelerations_conjugate']}",
        f"Diagnostic only: {payload['diagnostic_only']}",
        f"Uses source-derived metric branch: {payload['uses_source_derived_metric_branch']}",
        f"Uses same-L transport: {payload['uses_same_l_transport']}",
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
