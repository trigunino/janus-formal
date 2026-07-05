"""Active normalization helpers for Z2/Sigma background components."""

from __future__ import annotations

from dataclasses import dataclass

from .physical_units import G_SI, hubble_si


@dataclass(frozen=True)
class Z2SigmaCriticalNormalization:
    h0_z2sigma_km_s_mpc: float
    gravitational_constant_si_z2sigma: float = G_SI

    def __post_init__(self) -> None:
        if self.h0_z2sigma_km_s_mpc <= 0.0:
            raise ValueError("h0_z2sigma_km_s_mpc must be positive")
        if self.gravitational_constant_si_z2sigma <= 0.0:
            raise ValueError("gravitational_constant_si_z2sigma must be positive")

    @property
    def rho_crit0_kg_m3(self) -> float:
        h0_si = hubble_si(self.h0_z2sigma_km_s_mpc)
        return float(3.0 * h0_si**2 / (8.0 * 3.141592653589793 * self.gravitational_constant_si_z2sigma))

    @property
    def kappa_si(self) -> float:
        return 8.0 * 3.141592653589793 * self.gravitational_constant_si_z2sigma

    @property
    def kappa_rho_crit0_si(self) -> float:
        return self.kappa_si * self.rho_crit0_kg_m3


def make_active_z2sigma_critical_normalization(
    h0_z2sigma_km_s_mpc: float,
    *,
    gravitational_constant_si_z2sigma: float = G_SI,
) -> Z2SigmaCriticalNormalization:
    """Build active critical normalization from explicit Z2/Sigma inputs only."""

    return Z2SigmaCriticalNormalization(
        h0_z2sigma_km_s_mpc=float(h0_z2sigma_km_s_mpc),
        gravitational_constant_si_z2sigma=float(gravitational_constant_si_z2sigma),
    )
