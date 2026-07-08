from __future__ import annotations

from dataclasses import dataclass
from math import sqrt

import numpy as np

from .models import JanusExpansion, janus_distance_modulus_proxy


@dataclass(frozen=True)
class JanusExtended2026PublishedBackground:
    """Strict published background layer for the Janus 2024-2026 cosmology branch.

    This object carries only relations already anchored in the active source set:
    - M18 exact plus-branch shape and SN proxy
    - M18 open-marker distance relations
    - X2026 variable-constants gauge exponents

    It does not build a strict minus-sector history and it does not close a
    native BAO ruler.
    """

    q0: float = -0.087
    h0_km_s_mpc: float = 70.0
    q0_anchor: str = "M18 Eq. 6"
    exact_shape_anchor: str = "M18 Eq. 10"
    deceleration_anchor: str = "M18 Eq. 13"
    open_distance_anchor: str = "M18 Eqs. 14-17 and 20-21"
    h0_anchor: str = "EPJC 2024 observational discussion"
    variable_constants_anchor: str = "X2026-variable-constants Eq. 40"

    def __post_init__(self) -> None:
        if self.q0 >= 0.0:
            raise ValueError("q0 must be negative.")
        if self.h0_km_s_mpc <= 0.0:
            raise ValueError("h0_km_s_mpc must be positive.")

    @property
    def model(self) -> JanusExpansion:
        return JanusExpansion.from_q0(self.q0)

    @property
    def u0(self) -> float:
        return self.model.u0

    @property
    def z_max(self) -> float:
        return self.model.z_max

    def e_plus(self, z: float | np.ndarray) -> float | np.ndarray:
        return self.model.e(z)

    def sn_distance_modulus_proxy(self, z: float | np.ndarray) -> float | np.ndarray:
        return janus_distance_modulus_proxy(z, self.q0)

    def open_marker(self, z: float | np.ndarray) -> float | np.ndarray:
        z_arr = np.asarray(z, dtype=float)
        u_e = np.asarray(self.model.u_of_z(z_arr), dtype=float)
        marker = np.sinh(2.0 * (self.u0 - u_e))
        if np.isscalar(z):
            return float(np.asarray(marker))
        return marker

    def dm_unscaled_basis(self, z: float | np.ndarray) -> float | np.ndarray:
        basis = np.asarray(self.open_marker(z), dtype=float) / sqrt(1.0 - 2.0 * self.q0)
        if np.isscalar(z):
            return float(np.asarray(basis))
        return basis

    def dh_unscaled_basis(self, z: float | np.ndarray) -> float | np.ndarray:
        basis = 1.0 / np.asarray(self.e_plus(z), dtype=float)
        if np.isscalar(z):
            return float(np.asarray(basis))
        return basis

    def dv_unscaled_basis(self, z: float | np.ndarray) -> float | np.ndarray:
        z_arr = np.asarray(z, dtype=float)
        dm_basis = np.asarray(self.dm_unscaled_basis(z_arr), dtype=float)
        dh_basis = np.asarray(self.dh_unscaled_basis(z_arr), dtype=float)
        basis = np.cbrt(z_arr * dm_basis**2 * dh_basis)
        if np.isscalar(z):
            return float(np.asarray(basis))
        return basis

    @staticmethod
    def variable_constants_eq40_exponents() -> dict[str, float]:
        return {
            "c_hat": -0.5,
            "h_hat": 1.5,
            "g_hat": -1.0,
            "e_hat": 0.5,
            "m_hat": 1.0,
            "t_hat": 1.5,
            "mu0_hat": 1.0,
            "characteristic_length": 1.0,
        }

    @staticmethod
    def strict_blockers() -> tuple[str, ...]:
        return (
            "strict_minus_sector_history_not_closed_by_active_sources",
            "native_bao_ruler_not_closed_by_active_sources",
            "absolute_background_normalization_not_closed_by_active_sources",
            "full_cmb_observable_path_missing",
        )


def published_janus_extended2026_background() -> JanusExtended2026PublishedBackground:
    return JanusExtended2026PublishedBackground()
