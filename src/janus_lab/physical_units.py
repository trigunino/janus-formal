"""Physical calibration helpers for dimensionless PM prototypes."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


MPC_IN_METERS = 3.0856775814913673e22
SOLAR_MASS_KG = 1.98847e30
G_SI = 6.67430e-11
SECONDS_PER_GYR = 3.15576e16


def hubble_si(h0_km_s_mpc: float) -> float:
    if h0_km_s_mpc <= 0.0:
        raise ValueError("h0_km_s_mpc must be positive.")
    return h0_km_s_mpc * 1000.0 / MPC_IN_METERS


def hubble_time_gyr(h0_km_s_mpc: float) -> float:
    """Hubble time `1/H0` in Gyr."""

    return float(1.0 / hubble_si(h0_km_s_mpc) / SECONDS_PER_GYR)


def critical_density_kg_m3(h0_km_s_mpc: float) -> float:
    h0_si = hubble_si(h0_km_s_mpc)
    return float(3.0 * h0_si**2 / (8.0 * np.pi * G_SI))


def kg_m3_to_msun_mpc3(density_kg_m3: float) -> float:
    return float(density_kg_m3 * MPC_IN_METERS**3 / SOLAR_MASS_KG)


def critical_density_msun_mpc3(h0_km_s_mpc: float) -> float:
    return kg_m3_to_msun_mpc3(critical_density_kg_m3(h0_km_s_mpc))


def sigma8_radius_mpc(h0_km_s_mpc: float) -> float:
    return 8.0 / (h0_km_s_mpc / 100.0)


def pm_velocity_unit_km_s(box_size_mpc: float, time_unit_gyr: float) -> float:
    """Velocity unit for dimensionless PM velocities: box_size / time_unit."""

    if box_size_mpc <= 0.0:
        raise ValueError("box_size_mpc must be positive.")
    if time_unit_gyr <= 0.0:
        raise ValueError("time_unit_gyr must be positive.")
    return float(box_size_mpc * MPC_IN_METERS / (time_unit_gyr * SECONDS_PER_GYR) / 1000.0)


def pm_hubble_velocity_unit_km_s(box_size_mpc: float, h0_km_s_mpc: float) -> float:
    """PM velocity unit when code time is calibrated to `H0^-1`."""

    if box_size_mpc <= 0.0:
        raise ValueError("box_size_mpc must be positive.")
    return pm_velocity_unit_km_s(box_size_mpc, hubble_time_gyr(h0_km_s_mpc))


def pm_dimensionless_velocities_to_km_s(
    velocity_vectors: np.ndarray,
    box_size_mpc: float,
    time_unit_gyr: float,
) -> np.ndarray:
    """Convert dimensionless PM velocity vectors to km/s with explicit time unit."""

    return np.asarray(velocity_vectors, dtype=float) * pm_velocity_unit_km_s(
        box_size_mpc,
        time_unit_gyr,
    )


def minimum_grid_n_for_cell_size(box_size_mpc: float, max_cell_size_mpc: float) -> int:
    if box_size_mpc <= 0.0:
        raise ValueError("box_size_mpc must be positive.")
    if max_cell_size_mpc <= 0.0:
        raise ValueError("max_cell_size_mpc must be positive.")
    return int(np.ceil(box_size_mpc / max_cell_size_mpc))


def minimum_grid_n_for_smoothing_radius(
    box_size_mpc: float,
    radius_mpc: float,
    cells_per_radius: float = 2.0,
) -> int:
    if radius_mpc <= 0.0:
        raise ValueError("radius_mpc must be positive.")
    if cells_per_radius <= 0.0:
        raise ValueError("cells_per_radius must be positive.")
    return minimum_grid_n_for_cell_size(box_size_mpc, radius_mpc / cells_per_radius)


@dataclass(frozen=True)
class PhysicalBoxCalibration:
    box_size_mpc: float
    grid_shape: tuple[int, int, int]
    h0_km_s_mpc: float
    positive_omega_abs: float
    negative_omega_abs: float

    def __post_init__(self) -> None:
        if self.box_size_mpc <= 0.0:
            raise ValueError("box_size_mpc must be positive.")
        if len(self.grid_shape) != 3:
            raise ValueError("grid_shape must be three-dimensional.")
        if any(axis <= 0 for axis in self.grid_shape):
            raise ValueError("grid dimensions must be positive.")
        if self.positive_omega_abs < 0.0 or self.negative_omega_abs < 0.0:
            raise ValueError("sector omega values must be non-negative.")
        if self.positive_omega_abs + self.negative_omega_abs <= 0.0:
            raise ValueError("total absolute omega must be positive.")
        hubble_si(self.h0_km_s_mpc)

    @classmethod
    def from_total_absolute_omega(
        cls,
        box_size_mpc: float,
        grid_shape: tuple[int, int, int],
        h0_km_s_mpc: float = 70.0,
        omega_abs: float = 0.315,
        positive_fraction: float = 0.5,
    ) -> "PhysicalBoxCalibration":
        if omega_abs <= 0.0:
            raise ValueError("omega_abs must be positive.")
        if positive_fraction < 0.0 or positive_fraction > 1.0:
            raise ValueError("positive_fraction must be in [0, 1].")
        return cls(
            box_size_mpc=box_size_mpc,
            grid_shape=grid_shape,
            h0_km_s_mpc=h0_km_s_mpc,
            positive_omega_abs=omega_abs * positive_fraction,
            negative_omega_abs=omega_abs * (1.0 - positive_fraction),
        )

    @property
    def h(self) -> float:
        return self.h0_km_s_mpc / 100.0

    @property
    def critical_density_msun_mpc3(self) -> float:
        return critical_density_msun_mpc3(self.h0_km_s_mpc)

    @property
    def positive_density_msun_mpc3(self) -> float:
        return self.positive_omega_abs * self.critical_density_msun_mpc3

    @property
    def negative_abs_density_msun_mpc3(self) -> float:
        return self.negative_omega_abs * self.critical_density_msun_mpc3

    @property
    def total_abs_density_msun_mpc3(self) -> float:
        return self.positive_density_msun_mpc3 + self.negative_abs_density_msun_mpc3

    @property
    def volume_mpc3(self) -> float:
        return self.box_size_mpc**3

    @property
    def cell_size_mpc(self) -> tuple[float, float, float]:
        return tuple(self.box_size_mpc / axis for axis in self.grid_shape)

    @property
    def particle_count_per_sector(self) -> int:
        nx, ny, nz = self.grid_shape
        return nx * ny * nz

    @property
    def positive_particle_mass_msun(self) -> float:
        return self.positive_density_msun_mpc3 * self.volume_mpc3 / self.particle_count_per_sector

    @property
    def negative_abs_particle_mass_msun(self) -> float:
        return (
            self.negative_abs_density_msun_mpc3
            * self.volume_mpc3
            / self.particle_count_per_sector
        )

    @property
    def fundamental_mode_inv_mpc(self) -> float:
        return float(2.0 * np.pi / self.box_size_mpc)

    @property
    def nyquist_mode_inv_mpc(self) -> float:
        return float(np.pi / max(self.cell_size_mpc))

    @property
    def sigma8_radius_mpc(self) -> float:
        return sigma8_radius_mpc(self.h0_km_s_mpc)

    def resolves_radius(self, radius_mpc: float, cells_per_radius: float = 2.0) -> bool:
        if radius_mpc <= 0.0:
            raise ValueError("radius_mpc must be positive.")
        if cells_per_radius <= 0.0:
            raise ValueError("cells_per_radius must be positive.")
        return max(self.cell_size_mpc) <= radius_mpc / cells_per_radius

    def grid_n_required_for_radius(
        self,
        radius_mpc: float,
        cells_per_radius: float = 2.0,
    ) -> int:
        return minimum_grid_n_for_smoothing_radius(
            self.box_size_mpc,
            radius_mpc,
            cells_per_radius=cells_per_radius,
        )
