"""Kink-only growth ODE scaffold.

The solver encodes the mechanics of a derivative jump at a membrane crossing.
It does not derive or fit the kink coefficient.
"""

from __future__ import annotations

from collections.abc import Callable

import numpy as np


ScalarFunction = Callable[[float], float]


def default_omega_m_a(a: float, omega_m0: float = 0.3) -> float:
    if a <= 0.0:
        raise ValueError("a must be positive.")
    return float(omega_m0 * a**-3 / (omega_m0 * a**-3 + 1.0 - omega_m0))


def rk4_step(state: np.ndarray, x: float, dx: float, rhs: Callable[[float, np.ndarray], np.ndarray]) -> np.ndarray:
    k1 = rhs(x, state)
    k2 = rhs(x + 0.5 * dx, state + 0.5 * dx * k1)
    k3 = rhs(x + 0.5 * dx, state + 0.5 * dx * k2)
    k4 = rhs(x + dx, state + dx * k3)
    return state + dx * (k1 + 2.0 * k2 + 2.0 * k3 + k4) / 6.0


def integrate_kink_growth(
    *,
    k: float,
    a_initial: float,
    a_final: float,
    a_sigma: float,
    delta_initial: float = 1.0e-3,
    ddelta_initial: float = 1.0e-3,
    mu: ScalarFunction | None = None,
    omega_m: ScalarFunction | None = None,
    h_friction: ScalarFunction | None = None,
    s_kink: Callable[[float, float], float] | None = None,
    skink_coefficient_derived: bool = False,
    samples: int = 256,
) -> list[dict]:
    if k < 0.0 or not (0.0 < a_initial < a_final) or samples < 4:
        raise ValueError("invalid growth integration domain.")
    if not (a_initial < a_sigma < a_final):
        raise ValueError("a_sigma must lie inside the integration domain.")

    mu_func = mu or (lambda _a: 1.0)
    omega_func = omega_m or default_omega_m_a
    friction_func = h_friction or (lambda _a: 2.0)
    skink_func = s_kink or (lambda _k, _a: 0.0)
    x_grid = np.linspace(np.log(a_initial), np.log(a_final), samples)
    x_sigma = float(np.log(a_sigma))
    state = np.asarray([delta_initial, ddelta_initial], dtype=float)
    rows: list[dict] = []
    jump_applied = False

    def rhs(x: float, y: np.ndarray) -> np.ndarray:
        a = float(np.exp(x))
        return np.asarray(
            [
                y[1],
                -friction_func(a) * y[1] + 1.5 * omega_func(a) * mu_func(a) * y[0],
            ],
            dtype=float,
        )

    previous_x = float(x_grid[0])
    for x in x_grid:
        x_value = float(x)
        if x_value > previous_x:
            if previous_x < x_sigma <= x_value:
                state = rk4_step(state, previous_x, x_sigma - previous_x, rhs)
                jump = skink_func(k, a_sigma) if skink_coefficient_derived else 0.0
                state = np.asarray([state[0], state[1] + jump], dtype=float)
                jump_applied = True
                state = rk4_step(state, x_sigma, x_value - x_sigma, rhs)
            else:
                state = rk4_step(state, previous_x, x_value - previous_x, rhs)
        rows.append(
            {
                "a": float(np.exp(x_value)),
                "delta": float(state[0]),
                "ddelta_dln_a": float(state[1]),
                "jump_applied": jump_applied,
            }
        )
        previous_x = x_value
    return rows


def growth_prediction_ready(*, skink_coefficient_derived: bool, alpha_janus_derived: bool) -> bool:
    return bool(skink_coefficient_derived and alpha_janus_derived)
