"""Cosmological expansion models and distance helpers.

The Janus exact expansion implemented here follows the parametric relation
listed in D'Agostini & Petit 2018 (local source M18, Eq. 10):

    a(u) = alpha * cosh(u)^2
    t(u) = alpha / 2 * (1 + sinh(2u) / 2 + u)

Only ratios are used here, so alpha cancels. The present epoch is encoded by
``u0`` and must be fitted or justified before drawing scientific conclusions.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import numpy as np

from .constants import SPEED_OF_LIGHT_KM_S

ArrayLike = float | np.ndarray


def _as_array(z: ArrayLike) -> np.ndarray:
    return np.asarray(z, dtype=float)


def _maybe_scalar(original: ArrayLike, value: np.ndarray) -> ArrayLike:
    if np.isscalar(original):
        return float(np.asarray(value))
    return value


def e_lcdm(
    z: ArrayLike,
    omega_m: float = 0.315,
    omega_lambda: float | None = None,
    omega_k: float = 0.0,
    omega_r: float = 0.0,
) -> ArrayLike:
    """Dimensionless expansion rate E(z)=H(z)/H0 for Lambda-CDM."""

    z_arr = _as_array(z)
    if omega_lambda is None:
        omega_lambda = 1.0 - omega_m - omega_k - omega_r
    zp1 = 1.0 + z_arr
    e2 = (
        omega_r * zp1**4
        + omega_m * zp1**3
        + omega_k * zp1**2
        + omega_lambda
    )
    return _maybe_scalar(z, np.sqrt(e2))


def e_cpl(
    z: ArrayLike,
    omega_m: float = 0.315,
    w0: float = -1.0,
    wa: float = 0.0,
    omega_de: float | None = None,
    omega_k: float = 0.0,
    omega_r: float = 0.0,
) -> ArrayLike:
    """Dimensionless expansion rate for the CPL dark-energy parametrization."""

    z_arr = _as_array(z)
    if omega_de is None:
        omega_de = 1.0 - omega_m - omega_k - omega_r
    zp1 = 1.0 + z_arr
    de_evolution = zp1 ** (3.0 * (1.0 + w0 + wa)) * np.exp(
        -3.0 * wa * z_arr / zp1
    )
    e2 = (
        omega_r * zp1**4
        + omega_m * zp1**3
        + omega_k * zp1**2
        + omega_de * de_evolution
    )
    return _maybe_scalar(z, np.sqrt(e2))


def janus_q0_from_u0(u0: float) -> float:
    """Present-day Janus deceleration parameter.

    Source: local bibliography M18, Eq. 3 / 13.
    """

    if u0 <= 0:
        raise ValueError("u0 must be positive.")
    return float(-1.0 / (2.0 * np.sinh(u0) ** 2))


def janus_u0_from_q0(q0: float) -> float:
    """Invert q0 = -1/(2*sinh(u0)^2)."""

    if q0 >= 0:
        raise ValueError("q0 must be negative.")
    return float(np.arcsinh(np.sqrt(-1.0 / (2.0 * q0))))


def janus_distance_modulus_proxy(z: ArrayLike, q0: float) -> ArrayLike:
    """Janus SN magnitude-redshift proxy from D'Agostini & Petit (2018).

    Source: local bibliography M18, Eq. 5.

    The published relation is m_bol = 5 log10(distance_proxy) + cst,
    where cst is a fitted nuisance offset. This helper returns only the
    5*log10 term.
    """

    if q0 >= 0:
        raise ValueError("q0 must be negative.")
    z_arr = _as_array(z)
    radicand = 1.0 + 2.0 * q0 * z_arr
    if np.any(radicand <= 0.0):
        raise ValueError("Janus SN proxy requires 1 + 2*q0*z > 0.")
    proxy = z_arr + z_arr**2 * (1.0 - q0) / (
        1.0 + q0 * z_arr + np.sqrt(radicand)
    )
    with np.errstate(divide="ignore"):
        mu_like = 5.0 * np.log10(proxy)
    return _maybe_scalar(z, mu_like)


@dataclass(frozen=True)
class JanusExpansion:
    """Parametric Janus expansion law normalized at the present epoch.

    ``u0`` sets today's position on the parametric curve. With the normalization
    a(today)=1, the model has a maximum representable redshift:

        z_max = cosh(u0)^2 - 1

    For CMB-scale tests, ``u0`` must therefore be large enough.
    """

    u0: float = 4.0

    def __post_init__(self) -> None:
        if self.u0 <= 0:
            raise ValueError("u0 must be positive.")

    @classmethod
    def from_q0(cls, q0: float) -> "JanusExpansion":
        return cls(u0=janus_u0_from_q0(q0))

    @staticmethod
    def _shape(u: np.ndarray) -> np.ndarray:
        return np.cosh(u) ** 2

    @staticmethod
    def _h_shape(u: np.ndarray) -> np.ndarray:
        return np.sinh(2.0 * u) / (np.cosh(u) ** 4)

    @property
    def z_max(self) -> float:
        return float(self._shape(np.asarray(self.u0)) - 1.0)

    def u_of_z(self, z: ArrayLike) -> ArrayLike:
        z_arr = _as_array(z)
        if np.any(z_arr < 0):
            raise ValueError("JanusExpansion currently supports z >= 0 only.")
        if np.any(z_arr > self.z_max):
            raise ValueError(
                f"z exceeds this Janus normalization limit: z_max={self.z_max:.6g}"
            )
        target = self._shape(np.asarray(self.u0)) / (1.0 + z_arr)
        u = np.arccosh(np.sqrt(target))
        return _maybe_scalar(z, u)

    def e(self, z: ArrayLike) -> ArrayLike:
        """Dimensionless H(z)/H0 from the Janus parametric expansion."""

        u = _as_array(self.u_of_z(z))
        e = self._h_shape(u) / self._h_shape(np.asarray(self.u0))
        return _maybe_scalar(z, e)


def comoving_distance_mpc(
    z: ArrayLike,
    e_func: Callable[[ArrayLike], ArrayLike],
    h0: float = 70.0,
    samples: int = 2048,
) -> ArrayLike:
    """Line-of-sight comoving distance in Mpc for a flat FLRW-like model."""

    z_arr = _as_array(z)
    if np.any(z_arr < 0):
        raise ValueError("z must be non-negative.")

    flat_z = z_arr.reshape(-1)
    distances = np.empty_like(flat_z)
    for index, z_value in enumerate(flat_z):
        if z_value == 0:
            distances[index] = 0.0
            continue
        grid = np.linspace(0.0, z_value, samples)
        inv_e = 1.0 / _as_array(e_func(grid))
        trapz = getattr(np, "trapezoid", None)
        if trapz is None:
            trapz = np.trapz
        distances[index] = SPEED_OF_LIGHT_KM_S / h0 * trapz(inv_e, grid)

    result = distances.reshape(z_arr.shape)
    return _maybe_scalar(z, result)


def luminosity_distance_mpc(
    z: ArrayLike,
    e_func: Callable[[ArrayLike], ArrayLike],
    h0: float = 70.0,
    samples: int = 2048,
) -> ArrayLike:
    """Luminosity distance in Mpc for a flat FLRW-like model."""

    z_arr = _as_array(z)
    dc = _as_array(comoving_distance_mpc(z_arr, e_func, h0=h0, samples=samples))
    dl = (1.0 + z_arr) * dc
    return _maybe_scalar(z, dl)


def angular_diameter_distance_mpc(
    z: ArrayLike,
    e_func: Callable[[ArrayLike], ArrayLike],
    h0: float = 70.0,
    samples: int = 2048,
) -> ArrayLike:
    """Angular-diameter distance in Mpc for a flat FLRW-like model."""

    z_arr = _as_array(z)
    dc = _as_array(comoving_distance_mpc(z_arr, e_func, h0=h0, samples=samples))
    da = dc / (1.0 + z_arr)
    return _maybe_scalar(z, da)


def distance_modulus(
    z: ArrayLike,
    e_func: Callable[[ArrayLike], ArrayLike],
    h0: float = 70.0,
    samples: int = 2048,
) -> ArrayLike:
    """Distance modulus mu=5 log10(dL/Mpc)+25."""

    dl = _as_array(luminosity_distance_mpc(z, e_func, h0=h0, samples=samples))
    with np.errstate(divide="ignore"):
        mu = 5.0 * np.log10(dl) + 25.0
    return _maybe_scalar(z, mu)
