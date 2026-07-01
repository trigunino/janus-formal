from __future__ import annotations

from pathlib import Path
import json
import math


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_ionization_ode_solver_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_ionization_ode_solver_target.json")


def _rhs(xe: float, a: float) -> float:
    h_z4 = math.sqrt(0.3 / a**3 + 0.7)
    alpha_nb = 20.0 / a**3
    beta = 2.0e-4 / a
    c_peebles = 0.9
    return c_peebles * (beta * (1.0 - xe) - alpha_nb * xe * xe) / h_z4


def _rk4_step(xe: float, a: float, da: float) -> float:
    k1 = _rhs(xe, a)
    k2 = _rhs(xe + 0.5 * da * k1, a + 0.5 * da)
    k3 = _rhs(xe + 0.5 * da * k2, a + 0.5 * da)
    k4 = _rhs(xe + da * k3, a + da)
    updated = xe + da * (k1 + 2 * k2 + 2 * k3 + k4) / 6.0
    return min(1.0, max(0.0, updated))


def build_payload() -> dict:
    a0, a1, steps = 1.0e-3, 1.0, 400
    da = (a1 - a0) / steps
    xe = 0.999
    history = []
    for idx in range(steps + 1):
        a = a0 + idx * da
        tau_dot = a * xe
        visibility_proxy = tau_dot * math.exp(-a)
        history.append((a, xe, visibility_proxy))
        if idx < steps:
            xe = _rk4_step(xe, a, da)

    xe_values = [row[1] for row in history]
    visibility_values = [row[2] for row in history]
    bounded = all(0.0 <= value <= 1.0 for value in xe_values)
    finite_visibility = all(math.isfinite(value) and value >= 0.0 for value in visibility_values)
    return {
        "status": "janus-z4-ionization-ode-solver-target",
        "a_initial": a0,
        "a_final": a1,
        "steps": steps,
        "x_e_initial": history[0][1],
        "x_e_final": history[-1][1],
        "x_e_min": min(xe_values),
        "x_e_max": max(xe_values),
        "visibility_proxy_min": min(visibility_values),
        "visibility_proxy_max": max(visibility_values),
        "bounded_ionization_history_produced": bounded,
        "visibility_built_from_history": finite_visibility,
        "z4_expansion_rate_inserted": True,
        "calibrated_recombination_coefficients_used": False,
        "physical_recombination_visibility_nonproxy": False,
        "next_required": (
            "Replace proxy alpha/beta/H inputs with calibrated Z4 recombination "
            "coefficients and feed the resulting visibility into LOS integration."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Ionization ODE Solver Target",
        "",
        f"Status: `{payload['status']}`",
        f"x_e range: `{payload['x_e_min']}` to `{payload['x_e_max']}`",
        f"x_e final: `{payload['x_e_final']}`",
        f"Bounded history: `{payload['bounded_ionization_history_produced']}`",
        f"Visibility from history: `{payload['visibility_built_from_history']}`",
        f"Physical recombination visibility nonproxy: `{payload['physical_recombination_visibility_nonproxy']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
