"""Prototype initial-condition helpers for Janus PM diagnostics."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .field_statistics import pearson_correlation, rms, sigma_r_3d
from .poisson import (
    acceleration_from_potential_2d,
    acceleration_from_potential_3d,
    solve_periodic_poisson_2d,
    solve_periodic_poisson_3d,
)
from .signed_sector import BodyState, Sector


@dataclass(frozen=True)
class SectorContrastFields:
    positive_contrast: np.ndarray
    negative_contrast: np.ndarray


def _validate_grid(grid_shape: tuple[int, int], box_size: float) -> tuple[int, int]:
    if len(grid_shape) != 2:
        raise ValueError("grid_shape must be two-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny = grid_shape
    if nx <= 0 or ny <= 0:
        raise ValueError("grid dimensions must be positive.")
    return nx, ny


def _validate_grid_3d(
    grid_shape: tuple[int, int, int],
    box_size: float,
) -> tuple[int, int, int]:
    if len(grid_shape) != 3:
        raise ValueError("grid_shape must be three-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny, nz = grid_shape
    if nx <= 0 or ny <= 0 or nz <= 0:
        raise ValueError("grid dimensions must be positive.")
    return nx, ny, nz


def gaussian_random_field_2d(
    grid_shape: tuple[int, int],
    box_size: float,
    seed: int,
    target_rms: float,
    spectral_index: float = 0.0,
    cutoff_fraction: float = 0.5,
) -> np.ndarray:
    """Generate a reproducible real Gaussian-like field with controlled RMS."""

    nx, ny = _validate_grid(grid_shape, box_size)
    if target_rms < 0.0:
        raise ValueError("target_rms must be non-negative.")
    if cutoff_fraction <= 0.0:
        raise ValueError("cutoff_fraction must be positive.")
    if target_rms == 0.0:
        return np.zeros((nx, ny), dtype=float)

    rng = np.random.default_rng(seed)
    white = rng.normal(size=(nx, ny))
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kkx, kky = np.meshgrid(kx, ky, indexing="ij")
    radius = np.sqrt(kkx**2 + kky**2)
    k_min = 2.0 * np.pi / box_size
    k_cut = cutoff_fraction * np.max(radius)
    weight = np.zeros_like(radius)
    nonzero = radius > 0.0
    weight[nonzero] = (radius[nonzero] / k_min) ** (0.5 * spectral_index)
    weight[nonzero] *= np.exp(-0.5 * (radius[nonzero] / k_cut) ** 2)

    field = np.real(np.fft.ifftn(np.fft.fftn(white) * weight))
    field -= float(np.mean(field))
    field_rms = rms(field)
    if field_rms == 0.0:
        raise ValueError("generated field has zero variance.")
    return field * (target_rms / field_rms)


def gaussian_random_field_3d(
    grid_shape: tuple[int, int, int],
    box_size: float,
    seed: int,
    target_rms: float,
    spectral_index: float = 0.0,
    cutoff_fraction: float = 0.5,
) -> np.ndarray:
    """Generate a reproducible real 3D Gaussian-like field with controlled RMS."""

    nx, ny, nz = _validate_grid_3d(grid_shape, box_size)
    if target_rms < 0.0:
        raise ValueError("target_rms must be non-negative.")
    if cutoff_fraction <= 0.0:
        raise ValueError("cutoff_fraction must be positive.")
    if target_rms == 0.0:
        return np.zeros((nx, ny, nz), dtype=float)

    rng = np.random.default_rng(seed)
    white = rng.normal(size=(nx, ny, nz))
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kz = 2.0 * np.pi * np.fft.fftfreq(nz, d=box_size / nz)
    kkx, kky, kkz = np.meshgrid(kx, ky, kz, indexing="ij")
    radius = np.sqrt(kkx**2 + kky**2 + kkz**2)
    k_min = 2.0 * np.pi / box_size
    k_cut = cutoff_fraction * np.max(radius)
    weight = np.zeros_like(radius)
    nonzero = radius > 0.0
    weight[nonzero] = (radius[nonzero] / k_min) ** (0.5 * spectral_index)
    weight[nonzero] *= np.exp(-0.5 * (radius[nonzero] / k_cut) ** 2)

    field = np.real(np.fft.ifftn(np.fft.fftn(white) * weight))
    field -= float(np.mean(field))
    field_rms = rms(field)
    if field_rms == 0.0:
        raise ValueError("generated field has zero variance.")
    return field * (target_rms / field_rms)


def paired_sector_contrasts(
    grid_shape: tuple[int, int],
    box_size: float,
    seed: int,
    target_rms: float,
    spectral_index: float = 0.0,
    anti_correlation: float = 1.0,
) -> SectorContrastFields:
    if anti_correlation < 0.0 or anti_correlation > 1.0:
        raise ValueError("anti_correlation must be in [0, 1].")
    positive = gaussian_random_field_2d(
        grid_shape,
        box_size,
        seed=seed,
        target_rms=target_rms,
        spectral_index=spectral_index,
    )
    if anti_correlation == 1.0:
        negative = -positive
    else:
        independent = gaussian_random_field_2d(
            grid_shape,
            box_size,
            seed=seed + 1,
            target_rms=target_rms,
            spectral_index=spectral_index,
        )
        negative = -anti_correlation * positive + np.sqrt(1.0 - anti_correlation**2) * independent
        negative -= float(np.mean(negative))
        negative *= target_rms / rms(negative)
    return SectorContrastFields(positive_contrast=positive, negative_contrast=negative)


def paired_sector_contrasts_3d(
    grid_shape: tuple[int, int, int],
    box_size: float,
    seed: int,
    target_rms: float,
    spectral_index: float = 0.0,
    anti_correlation: float = 1.0,
) -> SectorContrastFields:
    if anti_correlation < 0.0 or anti_correlation > 1.0:
        raise ValueError("anti_correlation must be in [0, 1].")
    positive = gaussian_random_field_3d(
        grid_shape,
        box_size,
        seed=seed,
        target_rms=target_rms,
        spectral_index=spectral_index,
    )
    if anti_correlation == 1.0:
        negative = -positive
    else:
        independent = gaussian_random_field_3d(
            grid_shape,
            box_size,
            seed=seed + 1,
            target_rms=target_rms,
            spectral_index=spectral_index,
        )
        negative = -anti_correlation * positive + np.sqrt(1.0 - anti_correlation**2) * independent
        negative -= float(np.mean(negative))
        negative *= target_rms / rms(negative)
    return SectorContrastFields(positive_contrast=positive, negative_contrast=negative)


def lognormal_contrast_from_gaussian(field: np.ndarray, amplitude: float) -> np.ndarray:
    if amplitude < 0.0:
        raise ValueError("amplitude must be non-negative.")
    values = np.asarray(field, dtype=float)
    centered = values - float(np.mean(values))
    exponent = amplitude * centered
    exponent -= float(np.max(exponent))
    density = np.exp(exponent)
    density /= float(np.mean(density))
    return density - 1.0


def paired_lognormal_sector_contrasts_3d(
    gaussian_field: np.ndarray,
    amplitude: float,
) -> SectorContrastFields:
    values = np.asarray(gaussian_field, dtype=float)
    if values.ndim != 3:
        raise ValueError("gaussian_field must be three-dimensional.")
    return SectorContrastFields(
        positive_contrast=lognormal_contrast_from_gaussian(values, amplitude),
        negative_contrast=lognormal_contrast_from_gaussian(-values, amplitude),
    )


def paired_lognormal_contrasts_for_sigma_r_3d(
    gaussian_field: np.ndarray,
    box_size: float,
    radius: float,
    target_sigma: float,
    tolerance: float = 1e-4,
    max_iterations: int = 32,
) -> tuple[SectorContrastFields, float]:
    if target_sigma < 0.0:
        raise ValueError("target_sigma must be non-negative.")
    if target_sigma == 0.0:
        zeros = np.zeros_like(np.asarray(gaussian_field, dtype=float))
        return SectorContrastFields(positive_contrast=zeros, negative_contrast=zeros), 0.0
    low = 0.0
    high = 1.0
    while True:
        high_fields = paired_lognormal_sector_contrasts_3d(gaussian_field, high)
        high_sigma = sigma_r_3d(high_fields.positive_contrast, box_size, radius)
        if high_sigma >= target_sigma:
            break
        high *= 2.0
        if high > 128.0:
            raise ValueError("could not bracket target sigma_R.")

    best_fields = high_fields
    best_amplitude = high
    for _ in range(max_iterations):
        mid = 0.5 * (low + high)
        fields = paired_lognormal_sector_contrasts_3d(gaussian_field, mid)
        sigma = sigma_r_3d(fields.positive_contrast, box_size, radius)
        best_fields = fields
        best_amplitude = mid
        if abs(sigma - target_sigma) <= tolerance * target_sigma:
            break
        if sigma < target_sigma:
            low = mid
        else:
            high = mid
    return best_fields, best_amplitude


def bounded_anticorrelated_contrasts_3d(
    gaussian_field: np.ndarray,
    shape_amplitude: float,
    max_abs_contrast: float = 0.999,
) -> SectorContrastFields:
    if shape_amplitude < 0.0:
        raise ValueError("shape_amplitude must be non-negative.")
    if max_abs_contrast <= 0.0 or max_abs_contrast >= 1.0:
        raise ValueError("max_abs_contrast must be in (0, 1).")
    values = np.asarray(gaussian_field, dtype=float)
    if values.ndim != 3:
        raise ValueError("gaussian_field must be three-dimensional.")
    centered = values - float(np.mean(values))
    field_rms = rms(centered)
    if field_rms == 0.0 or shape_amplitude == 0.0:
        positive = np.zeros_like(values)
    else:
        raw = np.tanh(shape_amplitude * centered / field_rms)
        raw -= float(np.mean(raw))
        max_abs = float(np.max(np.abs(raw)))
        positive = np.zeros_like(values) if max_abs == 0.0 else max_abs_contrast * raw / max_abs
    return SectorContrastFields(positive_contrast=positive, negative_contrast=-positive)


def bounded_anticorrelated_contrasts_for_sigma_r_3d(
    gaussian_field: np.ndarray,
    box_size: float,
    radius: float,
    target_sigma: float,
    shape_amplitude: float,
    max_abs_contrast: float = 0.999,
) -> tuple[SectorContrastFields, float]:
    if target_sigma < 0.0:
        raise ValueError("target_sigma must be non-negative.")
    fields = bounded_anticorrelated_contrasts_3d(
        gaussian_field,
        shape_amplitude=shape_amplitude,
        max_abs_contrast=max_abs_contrast,
    )
    max_sigma = sigma_r_3d(fields.positive_contrast, box_size, radius)
    if target_sigma == 0.0:
        zeros = np.zeros_like(fields.positive_contrast)
        return SectorContrastFields(positive_contrast=zeros, negative_contrast=zeros), max_sigma
    if max_sigma == 0.0 or target_sigma > max_sigma:
        raise ValueError("target_sigma exceeds bounded contrast capacity.")
    scale = target_sigma / max_sigma
    positive = fields.positive_contrast * scale
    return SectorContrastFields(positive_contrast=positive, negative_contrast=-positive), max_sigma


def displacement_from_contrast(
    contrast: np.ndarray,
    box_size: float,
    displacement_scale: float,
) -> np.ndarray:
    if displacement_scale < 0.0:
        raise ValueError("displacement_scale must be non-negative.")
    values = np.asarray(contrast, dtype=float)
    if values.ndim != 2:
        raise ValueError("contrast must be two-dimensional.")
    if displacement_scale == 0.0:
        return np.zeros(values.shape + (2,), dtype=float)
    potential = solve_periodic_poisson_2d(
        values,
        box_size=box_size,
        gravitational_constant=1.0 / (4.0 * np.pi),
        subtract_mean=True,
    )
    ax, ay = acceleration_from_potential_2d(potential, box_size=box_size)
    return displacement_scale * np.stack((ax, ay), axis=-1)


def displacement_from_contrast_3d(
    contrast: np.ndarray,
    box_size: float,
    displacement_scale: float,
) -> np.ndarray:
    if displacement_scale < 0.0:
        raise ValueError("displacement_scale must be non-negative.")
    values = np.asarray(contrast, dtype=float)
    if values.ndim != 3:
        raise ValueError("contrast must be three-dimensional.")
    if displacement_scale == 0.0:
        return np.zeros(values.shape + (3,), dtype=float)
    potential = solve_periodic_poisson_3d(
        values,
        box_size=box_size,
        gravitational_constant=1.0 / (4.0 * np.pi),
        subtract_mean=True,
    )
    ax, ay, az = acceleration_from_potential_3d(potential, box_size=box_size)
    return displacement_scale * np.stack((ax, ay, az), axis=-1)


def lattice_bodies_from_displacement(
    displacement: np.ndarray,
    sector: Sector,
    box_size: float,
    mass_abs: float = 1.0,
) -> list[BodyState]:
    if mass_abs < 0.0:
        raise ValueError("mass_abs must be non-negative.")
    values = np.asarray(displacement, dtype=float)
    if values.ndim != 3 or values.shape[2] != 2:
        raise ValueError("displacement must have shape (nx, ny, 2).")
    nx, ny = _validate_grid(values.shape[:2], box_size)
    x = (np.arange(nx) + 0.5) * box_size / nx
    y = (np.arange(ny) + 0.5) * box_size / ny
    bodies: list[BodyState] = []
    for i, x_value in enumerate(x):
        for j, y_value in enumerate(y):
            position = np.mod(np.asarray([x_value, y_value]) + values[i, j], box_size)
            bodies.append(BodyState(position, np.zeros(2), mass_abs, sector))
    return bodies


def lattice_bodies_from_displacement_3d(
    displacement: np.ndarray,
    sector: Sector,
    box_size: float,
    mass_abs: float = 1.0,
) -> list[BodyState]:
    if mass_abs < 0.0:
        raise ValueError("mass_abs must be non-negative.")
    values = np.asarray(displacement, dtype=float)
    if values.ndim != 4 or values.shape[3] != 3:
        raise ValueError("displacement must have shape (nx, ny, nz, 3).")
    nx, ny, nz = _validate_grid_3d(values.shape[:3], box_size)
    x = (np.arange(nx) + 0.5) * box_size / nx
    y = (np.arange(ny) + 0.5) * box_size / ny
    z = (np.arange(nz) + 0.5) * box_size / nz
    bodies: list[BodyState] = []
    for i, x_value in enumerate(x):
        for j, y_value in enumerate(y):
            for k, z_value in enumerate(z):
                base = np.asarray([x_value, y_value, z_value])
                position = np.mod(base + values[i, j, k], box_size)
                bodies.append(BodyState(position, np.zeros(3), mass_abs, sector))
    return bodies


def two_sector_lattice_initial_conditions(
    fields: SectorContrastFields,
    box_size: float,
    displacement_scale: float,
    mass_abs: float = 1.0,
) -> list[BodyState]:
    if fields.positive_contrast.shape != fields.negative_contrast.shape:
        raise ValueError("sector contrast fields must have the same shape.")
    positive_displacement = displacement_from_contrast(
        fields.positive_contrast,
        box_size=box_size,
        displacement_scale=displacement_scale,
    )
    negative_displacement = displacement_from_contrast(
        fields.negative_contrast,
        box_size=box_size,
        displacement_scale=displacement_scale,
    )
    return lattice_bodies_from_displacement(
        positive_displacement,
        Sector.POSITIVE,
        box_size=box_size,
        mass_abs=mass_abs,
    ) + lattice_bodies_from_displacement(
        negative_displacement,
        Sector.NEGATIVE,
        box_size=box_size,
        mass_abs=mass_abs,
    )


def two_sector_lattice_initial_conditions_3d(
    fields: SectorContrastFields,
    box_size: float,
    displacement_scale: float,
    mass_abs: float = 1.0,
) -> list[BodyState]:
    if fields.positive_contrast.shape != fields.negative_contrast.shape:
        raise ValueError("sector contrast fields must have the same shape.")
    positive_displacement = displacement_from_contrast_3d(
        fields.positive_contrast,
        box_size=box_size,
        displacement_scale=displacement_scale,
    )
    negative_displacement = displacement_from_contrast_3d(
        fields.negative_contrast,
        box_size=box_size,
        displacement_scale=displacement_scale,
    )
    return lattice_bodies_from_displacement_3d(
        positive_displacement,
        Sector.POSITIVE,
        box_size=box_size,
        mass_abs=mass_abs,
    ) + lattice_bodies_from_displacement_3d(
        negative_displacement,
        Sector.NEGATIVE,
        box_size=box_size,
        mass_abs=mass_abs,
    )


def sector_contrast_correlation(fields: SectorContrastFields) -> float:
    return pearson_correlation(fields.positive_contrast, fields.negative_contrast)
