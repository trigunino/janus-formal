from __future__ import annotations

import json
from dataclasses import dataclass
from math import acosh, cosh, sinh
from pathlib import Path

import numpy as np

from .janus_2024_reference import Janus2024FLRWReference
from .lensing import flrw_metric_determinant_ratio_factor


@dataclass(frozen=True)
class Janus2024AbsoluteNormalizationContract:
    """Paper-grade bulk normalization contract for the 2024 Janus reference."""

    e_global: float
    rho_plus0_kg_m3: float
    rho_minus0_kg_m3: float
    c_plus_m_s: float
    c_minus_m_s: float
    g_si: float
    rho_minus0_over_rho_plus0: float

    def to_reference(self) -> Janus2024FLRWReference:
        return Janus2024FLRWReference(
            e_global=self.e_global,
            rho_plus0_kg_m3=self.rho_plus0_kg_m3,
            rho_minus0_kg_m3=self.rho_minus0_kg_m3,
            c_plus_m_s=self.c_plus_m_s,
            c_minus_m_s=self.c_minus_m_s,
            g_si=self.g_si,
        )


def load_janus_2024_reference_from_normalization(
    path: str | Path,
    *,
    e_global: float,
    c_plus_m_s: float,
    c_minus_m_s: float,
    g_si: float,
) -> Janus2024FLRWReference:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    return Janus2024FLRWReference(
        e_global=float(e_global),
        rho_plus0_kg_m3=float(data["rho_plus0_abs_kg_m3"]),
        rho_minus0_kg_m3=float(data["rho_minus0_abs_kg_m3"]),
        c_plus_m_s=c_plus_m_s,
        c_minus_m_s=c_minus_m_s,
        g_si=g_si,
    )


def absolute_normalization_contract_from_payload(
    payload: dict,
    *,
    e_global: float,
    c_plus_m_s: float,
    c_minus_m_s: float,
    g_si: float,
) -> Janus2024AbsoluteNormalizationContract:
    return Janus2024AbsoluteNormalizationContract(
        e_global=float(e_global),
        rho_plus0_kg_m3=float(payload["rho_plus0_abs_kg_m3"]),
        rho_minus0_kg_m3=float(payload["rho_minus0_abs_kg_m3"]),
        c_plus_m_s=float(c_plus_m_s),
        c_minus_m_s=float(c_minus_m_s),
        g_si=float(g_si),
        rho_minus0_over_rho_plus0=float(payload["rho_minus0_over_rho_plus0"]),
    )


@dataclass(frozen=True)
class Janus2024BulkObservablePath:
    """Observable wrapper based on solved two-metric bulk histories.

    This is the non-proxy path: observables come from bulk histories
    `(x0, a_plus, adot_plus, a_minus, adot_minus)`, not from `q0/u0`.
    """

    x0: np.ndarray
    a_plus: np.ndarray
    adot_plus: np.ndarray
    a_minus: np.ndarray
    adot_minus: np.ndarray

    def __post_init__(self) -> None:
        lengths = {
            len(self.x0),
            len(self.a_plus),
            len(self.adot_plus),
            len(self.a_minus),
            len(self.adot_minus),
        }
        if len(lengths) != 1:
            raise ValueError("all history arrays must have the same length.")
        if len(self.x0) < 2:
            raise ValueError("history must contain at least two points.")
        if np.any(np.diff(self.x0) <= 0.0):
            raise ValueError("x0 history must be strictly increasing.")
        if np.any(self.a_plus <= 0.0) or np.any(self.a_minus <= 0.0):
            raise ValueError("scale factors must stay positive.")
        if not np.isclose(self.a_plus[-1], 1.0):
            raise ValueError("a_plus history must be normalized to 1 at the endpoint.")
        if np.any(np.diff(self.a_plus) <= 0.0):
            raise ValueError("a_plus history must be monotone increasing for z mapping.")

    def redshift_grid(self) -> np.ndarray:
        return 1.0 / self.a_plus - 1.0

    def determinant_bridge(self) -> np.ndarray:
        return np.asarray(
            flrw_metric_determinant_ratio_factor(self.a_plus, self.a_minus),
            dtype=float,
        )

    def determinant_weighted_cross_density(self, contract: Janus2024AbsoluteNormalizationContract) -> np.ndarray:
        bridge = self.determinant_bridge()
        rho_minus = contract.rho_minus0_kg_m3 / (self.a_minus**3)
        return bridge * rho_minus

    def h_plus_history(self) -> np.ndarray:
        return self.adot_plus / self.a_plus

    def h_minus_history(self) -> np.ndarray:
        return self.adot_minus / self.a_minus

    def e_plus(self, z: float | np.ndarray) -> float | np.ndarray:
        z_arr = np.asarray(z, dtype=float)
        z_hist = self.redshift_grid()
        order = np.argsort(z_hist)
        values = np.interp(z_arr, z_hist[order], self.h_plus_history()[order])
        h0 = float(self.h_plus_history()[-1])
        result = values / h0
        if np.isscalar(z):
            return float(np.asarray(result))
        return result

    def e_minus(self, z: float | np.ndarray) -> float | np.ndarray:
        z_arr = np.asarray(z, dtype=float)
        z_hist = self.redshift_grid()
        order = np.argsort(z_hist)
        values = np.interp(z_arr, z_hist[order], self.h_minus_history()[order])
        h0 = float(self.h_minus_history()[-1])
        result = values / h0
        if np.isscalar(z):
            return float(np.asarray(result))
        return result


def _rk4_step_2d(
    state: np.ndarray,
    x0: float,
    dx: float,
    rhs,
) -> np.ndarray:
    k1 = rhs(x0, state)
    k2 = rhs(x0 + 0.5 * dx, state + 0.5 * dx * k1)
    k3 = rhs(x0 + 0.5 * dx, state + 0.5 * dx * k2)
    k4 = rhs(x0 + dx, state + dx * k3)
    return state + (dx / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)


def _janus_exact_x0_seconds(alpha_seconds: float, u: np.ndarray) -> np.ndarray:
    return 0.5 * alpha_seconds * (0.5 * np.sinh(2.0 * u) + u)


def _janus_exact_normalized_a(u: np.ndarray, u0: float) -> np.ndarray:
    return (np.cosh(u) ** 2) / (cosh(u0) ** 2)


def _janus_exact_hubble(alpha_seconds: float, u: np.ndarray) -> np.ndarray:
    return np.sinh(2.0 * u) / (alpha_seconds * np.cosh(u) ** 4)


def build_cited_bulk_reference_path(
    *,
    reference: Janus2024FLRWReference,
    q0: float,
    h0_s_inv: float,
    alpha_seconds: float,
    z_max: float = 5.0,
    samples: int = 512,
    h_minus0_ratio: float | None = None,
) -> Janus2024BulkObservablePath:
    if z_max <= 0.0:
        raise ValueError("z_max must be positive.")
    if samples < 8:
        raise ValueError("samples must be at least 8.")
    u0 = float(np.arcsinh(np.sqrt(-1.0 / (2.0 * q0))))
    if h_minus0_ratio is None:
        h_minus0_ratio = 1.0 / (1.0 - 2.0 * q0)
    if h_minus0_ratio <= 0.0:
        raise ValueError("h_minus0_ratio must be positive.")
    a_min = 1.0 / (1.0 + z_max)
    u_min = acosh((cosh(u0) ** 2 / (1.0 + z_max)) ** 0.5)
    u_grid = np.linspace(u_min, u0, samples, dtype=float)

    x0_raw = _janus_exact_x0_seconds(alpha_seconds, u_grid)
    x0 = x0_raw - float(x0_raw[-1])
    a_plus = _janus_exact_normalized_a(u_grid, u0)
    h_plus = _janus_exact_hubble(alpha_seconds, u_grid)
    adot_plus = a_plus * h_plus

    if not np.isclose(a_plus[-1], 1.0):
        raise ValueError("exact plus-sector path must end at a_plus=1.")
    if not np.isclose(h_plus[-1], h0_s_inv):
        raise ValueError("exact plus-sector path must end at the cited H0.")

    present_to_past_x0 = x0[::-1]
    state = np.array([1.0, h_minus0_ratio * h0_s_inv], dtype=float)
    a_minus_desc = [float(state[0])]
    adot_minus_desc = [float(state[1])]

    def minus_rhs(current_x0: float, current_state: np.ndarray) -> np.ndarray:
        del current_x0
        a_minus, v_minus = current_state
        return np.array(
            [v_minus, reference.ddot_a_minus(float(a_minus))],
            dtype=float,
        )

    for index in range(len(present_to_past_x0) - 1):
        x_current = float(present_to_past_x0[index])
        dx = float(present_to_past_x0[index + 1] - present_to_past_x0[index])
        state = _rk4_step_2d(state, x_current, dx, minus_rhs)
        if state[0] <= 0.0:
            raise ValueError("minus-sector reference path became non-positive.")
        a_minus_desc.append(float(state[0]))
        adot_minus_desc.append(float(state[1]))

    a_minus = np.asarray(a_minus_desc[::-1], dtype=float)
    adot_minus = np.asarray(adot_minus_desc[::-1], dtype=float)
    if np.any(a_minus <= 0.0):
        raise ValueError("minus-sector path must remain positive.")

    return Janus2024BulkObservablePath(
        x0=np.asarray(x0, dtype=float),
        a_plus=np.asarray(a_plus, dtype=float),
        adot_plus=np.asarray(adot_plus, dtype=float),
        a_minus=a_minus,
        adot_minus=adot_minus,
    )
