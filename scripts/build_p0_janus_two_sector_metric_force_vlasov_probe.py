from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.vlasov_diagnostic import (
    gaussian_phase_space,
    solve_periodic_poisson_1d,
    strang_step_periodic,
    total_mass,
    velocity_moments,
)
from janus_lab.weakfield_geometry import slow_geodesic_acceleration_1d, weakfield_b4vol_1p1


REPORT_PATH = Path("outputs/reports/p0_janus_two_sector_metric_force_vlasov_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_two_sector_metric_force_vlasov_probe.json")


def build_payload() -> dict:
    nx = 64
    nv = 32
    box = 1.0
    x = (np.arange(nx) + 0.5) * box / nx
    v = np.linspace(-1.0, 1.0, nv, endpoint=False)
    dx = box / nx
    dv = v[1] - v[0]
    f_plus = gaussian_phase_space(x, v, x0=0.32, sigma_x=0.07, sigma_v=0.22, box_size=box)
    f_minus = gaussian_phase_space(x, v, x0=0.68, sigma_x=0.07, sigma_v=0.22, box_size=box)
    rho_plus = velocity_moments(f_plus, v, dv)["rho"]
    rho_minus = velocity_moments(f_minus, v, dv)["rho"]
    rho_eff = rho_plus - rho_minus
    phi_plus = solve_periodic_poisson_1d(rho_eff, box_size=box)
    phi_minus = -phi_plus
    psi = np.zeros_like(phi_plus)
    a_plus = slow_geodesic_acceleration_1d(phi_plus, psi, box)
    a_minus = slow_geodesic_acceleration_1d(phi_minus, psi, box)
    plus_next = strang_step_periodic(f_plus, v, a_plus, dt=0.001, dx=dx, dv=dv)
    minus_next = strang_step_periodic(f_minus, v, a_minus, dt=0.001, dx=dx, dv=dv)
    metrics = {
        "mass_plus_error": abs(total_mass(plus_next, dx, dv) - total_mass(f_plus, dx, dv)),
        "mass_minus_error": abs(total_mass(minus_next, dx, dv) - total_mass(f_minus, dx, dv)),
        "max_abs_phi_plus_plus_phi_minus": float(np.max(np.abs(phi_plus + phi_minus))),
        "max_abs_a_plus_plus_a_minus": float(np.max(np.abs(a_plus + a_minus))),
        "min_b4vol_plus_1p1": float(np.min(weakfield_b4vol_1p1(phi_plus, psi))),
        "min_b4vol_minus_1p1": float(np.min(weakfield_b4vol_1p1(phi_minus, psi))),
    }
    return {
        "description": "Diagnostic two-sector Vlasov step using weak-field metric-derived forces.",
        "status": "two-sector-metric-force-vlasov-probe-diagnostic",
        "depends_on": [
            "p0_janus_two_sector_vlasov_poisson_probe",
            "p0_janus_weakfield_metric_force_probe",
        ],
        "metrics": metrics,
        "rho_eff_to_phi_to_metric_force_chain_written": True,
        "sector_metric_forces_conjugate": metrics["max_abs_a_plus_plus_a_minus"] < 1e-12,
        "uses_source_selected_janus_metric": False,
        "uses_same_l_transport": False,
        "diagnostic_only": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": (
            "This links two-sector rho_eff to weak-field metric forces and Vlasov stepping. "
            "It is still a periodic diagnostic, not a source-selected Janus metric branch."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Two-Sector Metric-Force Vlasov Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "rho_eff to Phi to metric force chain written: "
        f"{payload['rho_eff_to_phi_to_metric_force_chain_written']}",
        f"Sector metric forces conjugate: {payload['sector_metric_forces_conjugate']}",
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
