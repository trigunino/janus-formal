from __future__ import annotations

from dataclasses import dataclass
from math import cosh, pi, sinh

from .constants import SPEED_OF_LIGHT_KM_S
from .janus_2024_bulk_path import Janus2024AbsoluteNormalizationContract
from .janus_2024_reference import Janus2024FLRWReference
from .models import janus_u0_from_q0
from .physical_units import G_SI, hubble_si


@dataclass(frozen=True)
class Janus2024CitedCalibration:
    """Published/cited background calibration bundle for the 2024 Janus paper."""

    q0: float
    h0_km_s_mpc: float
    rho_minus0_over_rho_plus0: float
    c_plus_m_s: float = SPEED_OF_LIGHT_KM_S * 1000.0
    c_minus_m_s: float = SPEED_OF_LIGHT_KM_S * 1000.0
    g_si: float = G_SI
    a_plus0_weight: float = 1.0
    a_minus0_weight: float = 1.0

    def __post_init__(self) -> None:
        if self.q0 >= 0.0:
            raise ValueError("q0 must be negative.")
        if self.h0_km_s_mpc <= 0.0:
            raise ValueError("h0_km_s_mpc must be positive.")
        if self.rho_minus0_over_rho_plus0 >= 0.0:
            raise ValueError("rho_minus0_over_rho_plus0 must be negative.")
        if self.c_plus_m_s <= 0.0 or self.c_minus_m_s <= 0.0:
            raise ValueError("sector light speeds must be positive.")
        if self.g_si <= 0.0:
            raise ValueError("g_si must be positive.")

    @property
    def h0_s_inv(self) -> float:
        return hubble_si(self.h0_km_s_mpc)

    @property
    def u0(self) -> float:
        return janus_u0_from_q0(self.q0)

    @property
    def alpha_seconds(self) -> float:
        u0 = self.u0
        return (2.0 * sinh(u0) * cosh(u0)) / (cosh(u0) ** 4 * self.h0_s_inv)

    @property
    def alpha_m(self) -> float:
        return self.alpha_seconds * self.c_plus_m_s

    @property
    def e_global_j(self) -> float:
        return self.q0 * self.h0_s_inv**2 * self.c_plus_m_s**2 / (4.0 * pi * self.g_si)

    @property
    def e_global_mass_kg(self) -> float:
        return self.e_global_j / (self.c_plus_m_s**2)

    def to_reference(self) -> Janus2024FLRWReference:
        return Janus2024FLRWReference.from_global_energy_and_ratio(
            e_global=self.e_global_j,
            rho_minus0_over_rho_plus0=self.rho_minus0_over_rho_plus0,
            c_plus_m_s=self.c_plus_m_s,
            c_minus_m_s=self.c_minus_m_s,
            g_si=self.g_si,
            a_plus0_weight=self.a_plus0_weight,
            a_minus0_weight=self.a_minus0_weight,
        )

    def to_normalization_contract(self) -> Janus2024AbsoluteNormalizationContract:
        reference = self.to_reference()
        return Janus2024AbsoluteNormalizationContract(
            e_global=self.e_global_j,
            rho_plus0_kg_m3=reference.rho_plus0_kg_m3,
            rho_minus0_kg_m3=reference.rho_minus0_kg_m3,
            c_plus_m_s=self.c_plus_m_s,
            c_minus_m_s=self.c_minus_m_s,
            g_si=self.g_si,
            rho_minus0_over_rho_plus0=self.rho_minus0_over_rho_plus0,
        )


def published_janus_2024_cited_calibration() -> Janus2024CitedCalibration:
    return Janus2024CitedCalibration(
        q0=-0.087,
        h0_km_s_mpc=70.0,
        rho_minus0_over_rho_plus0=-19.0,
    )
