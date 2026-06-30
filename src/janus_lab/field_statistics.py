"""Grid field statistics for Janus weak-field diagnostics."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class DensityFieldSummary:
    positive_contrast_rms: float
    negative_contrast_rms: float
    sector_correlation: float
    signed_contrast_rms: float


@dataclass(frozen=True)
class RadialPowerSpectrum:
    k_centers: np.ndarray
    power: np.ndarray
    mode_counts: np.ndarray


def density_contrast(density: np.ndarray) -> np.ndarray:
    values = np.asarray(density, dtype=float)
    mean = float(np.mean(values))
    if mean <= 0.0:
        raise ValueError("density mean must be positive.")
    return values / mean - 1.0


def rms(field: np.ndarray) -> float:
    values = np.asarray(field, dtype=float)
    return float(np.sqrt(np.mean(values**2)))


def pearson_correlation(first: np.ndarray, second: np.ndarray) -> float:
    first_values = np.asarray(first, dtype=float)
    second_values = np.asarray(second, dtype=float)
    if first_values.shape != second_values.shape:
        raise ValueError("fields must have the same shape.")
    first_centered = first_values.ravel() - float(np.mean(first_values))
    second_centered = second_values.ravel() - float(np.mean(second_values))
    denominator = float(np.linalg.norm(first_centered) * np.linalg.norm(second_centered))
    if denominator == 0.0:
        raise ValueError("correlation is undefined for constant fields.")
    return float(np.dot(first_centered, second_centered) / denominator)


def signed_sector_contrast(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
) -> np.ndarray:
    positive = np.asarray(positive_density_abs, dtype=float)
    negative = np.asarray(negative_density_abs, dtype=float)
    if positive.shape != negative.shape:
        raise ValueError("density fields must have the same shape.")
    scale = float(np.mean(positive + negative))
    if scale <= 0.0:
        raise ValueError("total density mean must be positive.")
    return (positive - negative) / scale


def density_field_summary(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
) -> DensityFieldSummary:
    positive_delta = density_contrast(positive_density_abs)
    negative_delta = density_contrast(negative_density_abs)
    return DensityFieldSummary(
        positive_contrast_rms=rms(positive_delta),
        negative_contrast_rms=rms(negative_delta),
        sector_correlation=pearson_correlation(positive_delta, negative_delta),
        signed_contrast_rms=rms(
            signed_sector_contrast(positive_density_abs, negative_density_abs)
        ),
    )


def radial_power_spectrum_2d(
    field: np.ndarray,
    box_size: float,
    bin_edges: np.ndarray,
) -> RadialPowerSpectrum:
    values = np.asarray(field, dtype=float)
    edges = np.asarray(bin_edges, dtype=float)
    if values.ndim != 2:
        raise ValueError("field must be two-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    if edges.ndim != 1 or len(edges) < 2:
        raise ValueError("bin_edges must be a one-dimensional array with at least two values.")
    if np.any(np.diff(edges) <= 0.0):
        raise ValueError("bin_edges must be strictly increasing.")

    nx, ny = values.shape
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kkx, kky = np.meshgrid(kx, ky, indexing="ij")
    radii = np.sqrt(kkx**2 + kky**2).ravel()
    centered = values - float(np.mean(values))
    power_values = (np.abs(np.fft.fftn(centered)) ** 2 / values.size**2).ravel()

    powers = []
    counts = []
    for left, right in zip(edges[:-1], edges[1:]):
        mask = (radii >= left) & (radii < right)
        counts.append(int(np.count_nonzero(mask)))
        powers.append(float(np.sum(power_values[mask])))
    return RadialPowerSpectrum(
        k_centers=0.5 * (edges[:-1] + edges[1:]),
        power=np.asarray(powers, dtype=float),
        mode_counts=np.asarray(counts, dtype=int),
    )


def radial_power_spectrum_3d(
    field: np.ndarray,
    box_size: float,
    bin_edges: np.ndarray,
) -> RadialPowerSpectrum:
    values = np.asarray(field, dtype=float)
    edges = np.asarray(bin_edges, dtype=float)
    if values.ndim != 3:
        raise ValueError("field must be three-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    if edges.ndim != 1 or len(edges) < 2:
        raise ValueError("bin_edges must be a one-dimensional array with at least two values.")
    if np.any(np.diff(edges) <= 0.0):
        raise ValueError("bin_edges must be strictly increasing.")

    nx, ny, nz = values.shape
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kz = 2.0 * np.pi * np.fft.fftfreq(nz, d=box_size / nz)
    kkx, kky, kkz = np.meshgrid(kx, ky, kz, indexing="ij")
    radii = np.sqrt(kkx**2 + kky**2 + kkz**2).ravel()
    centered = values - float(np.mean(values))
    power_values = (np.abs(np.fft.fftn(centered)) ** 2 / values.size**2).ravel()

    powers = []
    counts = []
    for left, right in zip(edges[:-1], edges[1:]):
        mask = (radii >= left) & (radii < right)
        counts.append(int(np.count_nonzero(mask)))
        powers.append(float(np.sum(power_values[mask])))
    return RadialPowerSpectrum(
        k_centers=0.5 * (edges[:-1] + edges[1:]),
        power=np.asarray(powers, dtype=float),
        mode_counts=np.asarray(counts, dtype=int),
    )


def spherical_tophat_window(k_radius: np.ndarray) -> np.ndarray:
    x = np.asarray(k_radius, dtype=float)
    window = np.ones_like(x)
    nonzero = np.abs(x) > 1e-8
    xn = x[nonzero]
    window[nonzero] = 3.0 * (np.sin(xn) - xn * np.cos(xn)) / xn**3
    return window


def sigma_r_3d(field: np.ndarray, box_size: float, radius: float) -> float:
    values = np.asarray(field, dtype=float)
    if values.ndim != 3:
        raise ValueError("field must be three-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    if radius <= 0.0:
        raise ValueError("radius must be positive.")

    nx, ny, nz = values.shape
    centered = values - float(np.mean(values))
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kz = 2.0 * np.pi * np.fft.fftfreq(nz, d=box_size / nz)
    k_radius = np.sqrt(
        kx[:, None, None] ** 2 + ky[None, :, None] ** 2 + kz[None, None, :] ** 2
    )
    smoothed = np.real(
        np.fft.ifftn(np.fft.fftn(centered) * spherical_tophat_window(k_radius * radius))
    )
    return rms(smoothed)


def normalize_field_to_sigma_r_3d(
    field: np.ndarray,
    box_size: float,
    radius: float,
    target_sigma: float,
) -> np.ndarray:
    if target_sigma < 0.0:
        raise ValueError("target_sigma must be non-negative.")
    values = np.asarray(field, dtype=float)
    current_sigma = sigma_r_3d(values, box_size=box_size, radius=radius)
    if current_sigma == 0.0:
        if target_sigma == 0.0:
            return np.zeros_like(values)
        raise ValueError("cannot normalize a field with zero sigma_R.")
    return values * (target_sigma / current_sigma)
