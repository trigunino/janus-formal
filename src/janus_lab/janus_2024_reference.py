from __future__ import annotations

from dataclasses import dataclass
from math import pi
import numpy as np


@dataclass(frozen=True)
class Janus2024PublishedDustBackground:
    """Paper-native FLRW dust background equations from EPJC 2024.

    This object carries only what the paper states explicitly:
    - two FLRW metrics with common chronological coordinate x0
    - compatibility / conserved energy relation
    - dust branch k = kbar = -1
    - exact dust acceleration equations (96a, 96b)

    It does not contain:
    - absolute density normalization
    - observational calibration
    - unique background history integration constants
    """

    common_time_coordinate: str = "x0"
    k_plus: int = -1
    k_minus: int = -1
    conservation_equation_anchor: str = "EPJC 2024 Eq. (94)"
    dust_branch_anchor: str = "EPJC 2024 Eq. (95)"
    acceleration_equations_anchor: str = "EPJC 2024 Eqs. (96a)-(96b)"

    def __post_init__(self) -> None:
        if self.k_plus != -1 or self.k_minus != -1:
            raise ValueError("Published Janus 2024 dust branch fixes k_plus = k_minus = -1.")

    @property
    def conservation_law(self) -> tuple[str, str]:
        return ("rho_plus * c_plus^2 * a_plus^3", "rho_minus * c_minus^2 * a_minus^3")

    def ddot_a_plus(self, *, a_plus: float, e_global: float, c_plus_m_s: float, g_si: float) -> float:
        if a_plus <= 0.0:
            raise ValueError("a_plus must be positive.")
        if c_plus_m_s <= 0.0 or g_si <= 0.0:
            raise ValueError("c_plus_m_s and g_si must be positive.")
        return -(4.0 * pi * g_si * e_global) / (c_plus_m_s**2 * a_plus**2)

    def ddot_a_minus(self, *, a_minus: float, e_global: float, c_minus_m_s: float, g_si: float) -> float:
        if a_minus <= 0.0:
            raise ValueError("a_minus must be positive.")
        if c_minus_m_s <= 0.0 or g_si <= 0.0:
            raise ValueError("c_minus_m_s and g_si must be positive.")
        return +(4.0 * pi * g_si * e_global) / (c_minus_m_s**2 * a_minus**2)


@dataclass(frozen=True)
class Janus2024PublishedObservationalAnchors:
    """Paper-native observational statements carried explicitly by EPJC 2024."""

    direct_standard_candle_h0_km_s_mpc: float = 70.0
    lcdm_cmb_h0_km_s_mpc: float = 67.0
    h0_anchor: str = "EPJC 2024 page 14 discussion before Eqs. (90-96)"
    magnitude_redshift_curve_claim_anchor: str = "EPJC 2024 page 3 and page 16"
    exact_fit_curve_claim_present: bool = True

    def __post_init__(self) -> None:
        if self.direct_standard_candle_h0_km_s_mpc <= 0.0:
            raise ValueError("direct_standard_candle_h0_km_s_mpc must be positive.")
        if self.lcdm_cmb_h0_km_s_mpc <= 0.0:
            raise ValueError("lcdm_cmb_h0_km_s_mpc must be positive.")


@dataclass(frozen=True)
class JanusPublishedExactShapeReference:
    """Published Janus exact shape layer with no absolute normalization.

    Source family: D'Agostini-Petit 2018 as cited by the Janus 2024 reference
    comparison figure and surrounding Janus expansion discussion.
    """

    q0: float = -0.087
    q0_anchor: str = "Published Janus SN fit value q0=-0.087"
    exact_shape_anchor: str = "Published Janus exact shape a(u) proportional cosh(u)^2"

    def __post_init__(self) -> None:
        if self.q0 >= 0.0:
            raise ValueError("q0 must be negative.")

    @property
    def u0(self) -> float:
        return float(np.arcsinh(np.sqrt(-1.0 / (2.0 * self.q0))))

    @staticmethod
    def a_shape(u: np.ndarray) -> np.ndarray:
        return np.cosh(u) ** 2

    @staticmethod
    def h_shape(u: np.ndarray) -> np.ndarray:
        return np.sinh(2.0 * u) / (np.cosh(u) ** 4)

    def normalized_a(self, u: float | np.ndarray) -> float | np.ndarray:
        value = self.a_shape(np.asarray(u, dtype=float)) / self.a_shape(np.asarray(self.u0))
        if np.isscalar(u):
            return float(np.asarray(value))
        return value

    def normalized_e(self, u: float | np.ndarray) -> float | np.ndarray:
        value = self.h_shape(np.asarray(u, dtype=float)) / self.h_shape(np.asarray(self.u0))
        if np.isscalar(u):
            return float(np.asarray(value))
        return value

    def u_of_z(self, z: float | np.ndarray) -> float | np.ndarray:
        z_arr = np.asarray(z, dtype=float)
        target = self.a_shape(np.asarray(self.u0)) / (1.0 + z_arr)
        value = np.arccosh(np.sqrt(target))
        if np.isscalar(z):
            return float(np.asarray(value))
        return value

    @property
    def z_max(self) -> float:
        return float(self.a_shape(np.asarray(self.u0)) - 1.0)

    def sample_normalized_plus_history(self, *, samples: int = 256) -> dict[str, np.ndarray]:
        if samples < 2:
            raise ValueError("samples must be at least 2.")
        u_grid = np.linspace(0.0, self.u0, samples, dtype=float)
        a_plus = np.asarray(self.normalized_a(u_grid), dtype=float)
        e_plus = np.asarray(self.normalized_e(u_grid), dtype=float)
        z_grid = 1.0 / a_plus - 1.0
        return {
            "u": u_grid,
            "a_plus": a_plus,
            "e_plus": e_plus,
            "z": z_grid,
        }


@dataclass(frozen=True)
class Janus2024PublishedCitedObservationReference:
    """Published observation-side Janus reference used by the 2024 paper.

    This is the positive-branch comparison layer:
    - cited Janus SN fit parameter q0=-0.087
    - EPJC 2024 direct-standard-candle H0=70 km/s/Mpc statement
    - exact plus-branch shape and distance-modulus proxy

    It is like-for-like with the published comparison logic, but it is not a
    full two-metric bulk solver.
    """

    q0: float = -0.087
    h0_km_s_mpc: float = 70.0
    q0_anchor: str = "Published/cited Janus SN fit q0=-0.087"
    h0_anchor: str = "EPJC 2024 direct-standard-candle H0=70 km/s/Mpc statement"

    def __post_init__(self) -> None:
        if self.q0 >= 0.0:
            raise ValueError("q0 must be negative.")
        if self.h0_km_s_mpc <= 0.0:
            raise ValueError("h0_km_s_mpc must be positive.")

    @property
    def u0(self) -> float:
        return float(np.arcsinh(np.sqrt(-1.0 / (2.0 * self.q0))))

    @property
    def h0_s_inv(self) -> float:
        mpc_m = 3.085677581491367e22
        return self.h0_km_s_mpc * 1000.0 / mpc_m

    @property
    def alpha_seconds(self) -> float:
        u0 = self.u0
        return float(np.sinh(2.0 * u0) / (np.cosh(u0) ** 4 * self.h0_s_inv))

    def distance_modulus_proxy(self, z: float | np.ndarray) -> float | np.ndarray:
        z_arr = np.asarray(z, dtype=float)
        radicand = 1.0 + 2.0 * self.q0 * z_arr
        if np.any(radicand <= 0.0):
            raise ValueError("published Janus SN proxy requires 1 + 2*q0*z > 0.")
        proxy = z_arr + z_arr**2 * (1.0 - self.q0) / (
            1.0 + self.q0 * z_arr + np.sqrt(radicand)
        )
        value = 5.0 * np.log10(proxy)
        if np.isscalar(z):
            return float(np.asarray(value))
        return value


@dataclass(frozen=True)
class Janus2024FLRWReference:
    """Minimal active bulk FLRW reference for The Janus Cosmological Model (2024).

    This is the paper-level homogeneous two-metric background object:
    - two scale factors: a_plus, a_minus
    - conserved global energy constant E
    - sector densities scaling as dust
    - paper branch k = kbar = -1

    It is an active equation container, not yet an observational wrapper.
    """

    e_global: float
    rho_plus0_kg_m3: float
    rho_minus0_kg_m3: float
    c_plus_m_s: float
    c_minus_m_s: float
    g_si: float
    k_plus: int = -1
    k_minus: int = -1

    def __post_init__(self) -> None:
        if self.k_plus != -1 or self.k_minus != -1:
            raise ValueError("Janus 2024 FLRW reference uses k_plus = k_minus = -1.")
        if self.rho_plus0_kg_m3 <= 0.0:
            raise ValueError("rho_plus0_kg_m3 must be positive.")
        if self.rho_minus0_kg_m3 >= 0.0:
            raise ValueError("rho_minus0_kg_m3 must be negative.")
        if self.c_plus_m_s <= 0.0 or self.c_minus_m_s <= 0.0:
            raise ValueError("sector light speeds must be positive.")
        if self.g_si <= 0.0:
            raise ValueError("g_si must be positive.")

    @classmethod
    def from_global_energy_and_ratio(
        cls,
        *,
        e_global: float,
        rho_minus0_over_rho_plus0: float,
        c_plus_m_s: float,
        c_minus_m_s: float,
        g_si: float,
        a_plus0_weight: float = 1.0,
        a_minus0_weight: float = 1.0,
    ) -> "Janus2024FLRWReference":
        denominator = (
            c_plus_m_s**2 * a_plus0_weight
            + rho_minus0_over_rho_plus0 * c_minus_m_s**2 * a_minus0_weight
        )
        if denominator == 0.0:
            raise ValueError("global-energy denominator is zero.")
        rho_plus0 = e_global / denominator
        rho_minus0 = rho_minus0_over_rho_plus0 * rho_plus0
        return cls(
            e_global=e_global,
            rho_plus0_kg_m3=rho_plus0,
            rho_minus0_kg_m3=rho_minus0,
            c_plus_m_s=c_plus_m_s,
            c_minus_m_s=c_minus_m_s,
            g_si=g_si,
        )

    def rho_plus(self, a_plus: float) -> float:
        if a_plus <= 0.0:
            raise ValueError("a_plus must be positive.")
        return self.rho_plus0_kg_m3 / (a_plus**3)

    def rho_minus(self, a_minus: float) -> float:
        if a_minus <= 0.0:
            raise ValueError("a_minus must be positive.")
        return self.rho_minus0_kg_m3 / (a_minus**3)

    def conserved_energy(self, a_plus: float, a_minus: float) -> float:
        return (
            self.rho_plus(a_plus) * self.c_plus_m_s**2 * a_plus**3
            + self.rho_minus(a_minus) * self.c_minus_m_s**2 * a_minus**3
        )

    def ddot_a_plus(self, a_plus: float) -> float:
        if a_plus <= 0.0:
            raise ValueError("a_plus must be positive.")
        return -(4.0 * pi * self.g_si * self.e_global) / (
            self.c_plus_m_s**2 * a_plus**2
        )

    def ddot_a_minus(self, a_minus: float) -> float:
        if a_minus <= 0.0:
            raise ValueError("a_minus must be positive.")
        return +(4.0 * pi * self.g_si * self.e_global) / (
            self.c_minus_m_s**2 * a_minus**2
        )

    def rhs(self, x0: float, state: tuple[float, float, float, float]) -> tuple[float, float, float, float]:
        del x0
        a_plus, v_plus, a_minus, v_minus = state
        return (
            v_plus,
            self.ddot_a_plus(a_plus),
            v_minus,
            self.ddot_a_minus(a_minus),
        )
