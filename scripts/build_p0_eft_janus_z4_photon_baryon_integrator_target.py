from __future__ import annotations

from pathlib import Path
import json
import math


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_photon_baryon_integrator_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_photon_baryon_integrator_target.json")


def _rhs(state: tuple[float, float, float], eta: float) -> tuple[float, float, float]:
    theta0, theta_gamma, theta_b = state
    k = 0.12
    tau_dot = 15.0 / (1.0 + eta)
    baryon_loading = 0.75
    phi_z4 = 1.0e-5 * math.exp(-0.1 * eta)
    psi_z4 = 0.8e-5 * math.exp(-0.1 * eta)
    d_theta0 = -theta_gamma / 3.0
    d_theta_gamma = k * k * (theta0 + phi_z4) + tau_dot * (theta_b - theta_gamma)
    d_theta_b = -0.02 * theta_b + k * k * psi_z4 + tau_dot * (theta_gamma - theta_b) / baryon_loading
    return d_theta0, d_theta_gamma, d_theta_b


def _step(state: tuple[float, float, float], eta: float, h: float) -> tuple[float, float, float]:
    def add(a: tuple[float, float, float], b: tuple[float, float, float], scale: float) -> tuple[float, float, float]:
        return tuple(x + scale * y for x, y in zip(a, b))  # type: ignore[return-value]

    k1 = _rhs(state, eta)
    k2 = _rhs(add(state, k1, 0.5 * h), eta + 0.5 * h)
    k3 = _rhs(add(state, k2, 0.5 * h), eta + 0.5 * h)
    k4 = _rhs(add(state, k3, h), eta + h)
    return tuple(
        x + h * (a + 2 * b + 2 * c + d) / 6.0
        for x, a, b, c, d in zip(state, k1, k2, k3, k4)
    )  # type: ignore[return-value]


def build_payload() -> dict:
    eta0, eta1, steps = 0.0, 20.0, 400
    h = (eta1 - eta0) / steps
    state = (1.0e-5, 0.0, 0.0)
    trajectory = []
    for idx in range(steps + 1):
        eta = eta0 + idx * h
        trajectory.append((eta, *state))
        if idx < steps:
            state = _step(state, eta, h)

    values = [value for row in trajectory for value in row[1:]]
    finite = all(math.isfinite(value) for value in values)
    bounded = all(abs(value) < 1.0e-2 for value in values)
    return {
        "status": "janus-z4-photon-baryon-integrator-target",
        "eta_initial": eta0,
        "eta_final": eta1,
        "steps": steps,
        "final_theta0": trajectory[-1][1],
        "final_theta_gamma": trajectory[-1][2],
        "final_theta_b": trajectory[-1][3],
        "max_abs_state": max(abs(value) for value in values),
        "finite_trajectory_produced": finite,
        "single_sector_limit_stable": bounded,
        "z4_metric_sources_inserted": True,
        "thomson_drag_inserted": True,
        "calibrated_boltzmann_integrator_executed": False,
        "photon_baryon_hierarchy_nonproxy": False,
        "next_required": (
            "Replace this finite RK target with the calibrated photon-baryon "
            "Boltzmann hierarchy using action-derived Z4 sources."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Photon-Baryon Integrator Target",
        "",
        f"Status: `{payload['status']}`",
        f"Max abs state: `{payload['max_abs_state']}`",
        f"Finite trajectory: `{payload['finite_trajectory_produced']}`",
        f"Single-sector stable: `{payload['single_sector_limit_stable']}`",
        f"Photon-baryon hierarchy nonproxy: `{payload['photon_baryon_hierarchy_nonproxy']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
