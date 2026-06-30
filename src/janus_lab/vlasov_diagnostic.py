"""Diagnostic 1D-1V Vlasov helpers.

This module is a numerical scaffold only. It does not encode a closed Janus
metric branch, same-L map, or physical phase-space measure.
"""

from __future__ import annotations

import numpy as np


def _validate_uniform_grid(values: np.ndarray, name: str) -> tuple[np.ndarray, float]:
    grid = np.asarray(values, dtype=float)
    if grid.ndim != 1 or grid.size < 2:
        raise ValueError(f"{name} must be a one-dimensional grid with at least two points.")
    diffs = np.diff(grid)
    if not np.allclose(diffs, diffs[0]):
        raise ValueError(f"{name} must be uniformly spaced.")
    return grid, float(diffs[0])


def _periodic_interp_axis0(values: np.ndarray, shifts: np.ndarray, spacing: float) -> np.ndarray:
    n = values.shape[0]
    index_shift = shifts / spacing
    base = np.arange(n, dtype=float)[:, None] - index_shift[None, :]
    i0 = np.floor(base).astype(int)
    frac = base - i0
    return (1.0 - frac) * values[i0 % n, np.arange(values.shape[1])] + frac * values[
        (i0 + 1) % n,
        np.arange(values.shape[1]),
    ]


def advect_x_periodic(distribution: np.ndarray, velocities: np.ndarray, dt: float, dx: float) -> np.ndarray:
    """Semi-Lagrangian periodic x-advection for `df/dt + v df/dx = 0`."""

    f = np.asarray(distribution, dtype=float)
    v = np.asarray(velocities, dtype=float)
    if f.ndim != 2:
        raise ValueError("distribution must have shape (nx, nv).")
    if v.shape != (f.shape[1],):
        raise ValueError("velocities must have shape (nv,).")
    if dx <= 0.0:
        raise ValueError("dx must be positive.")
    return _periodic_interp_axis0(f, v * dt, dx)


def advect_v_periodic(distribution: np.ndarray, acceleration: np.ndarray, dt: float, dv: float) -> np.ndarray:
    """Semi-Lagrangian periodic velocity-advection for `df/dt + a df/dv = 0`."""

    f = np.asarray(distribution, dtype=float)
    a = np.asarray(acceleration, dtype=float)
    if f.ndim != 2:
        raise ValueError("distribution must have shape (nx, nv).")
    if a.shape != (f.shape[0],):
        raise ValueError("acceleration must have shape (nx,).")
    if dv <= 0.0:
        raise ValueError("dv must be positive.")
    return _periodic_interp_axis0(f.T, a * dt, dv).T


def strang_step_periodic(
    distribution: np.ndarray,
    velocities: np.ndarray,
    acceleration: np.ndarray,
    dt: float,
    dx: float,
    dv: float,
) -> np.ndarray:
    """One diagnostic Strang step on a periodic x/v box."""

    half_x = advect_x_periodic(distribution, velocities, 0.5 * dt, dx)
    full_v = advect_v_periodic(half_x, acceleration, dt, dv)
    return advect_x_periodic(full_v, velocities, 0.5 * dt, dx)


def velocity_moments(distribution: np.ndarray, velocities: np.ndarray, dv: float) -> dict[str, np.ndarray]:
    """Return 1D moments `rho`, `beta`, `P`, `p`, `Pi`, `Q` from a diagnostic f(x,v)."""

    f = np.asarray(distribution, dtype=float)
    v = np.asarray(velocities, dtype=float)
    if f.ndim != 2:
        raise ValueError("distribution must have shape (nx, nv).")
    if v.shape != (f.shape[1],):
        raise ValueError("velocities must have shape (nv,).")
    if dv <= 0.0:
        raise ValueError("dv must be positive.")
    rho = np.sum(f, axis=1) * dv
    momentum = np.sum(f * v[None, :], axis=1) * dv
    beta = np.divide(momentum, rho, out=np.zeros_like(momentum), where=rho > 0.0)
    centered = v[None, :] - beta[:, None]
    pressure = np.sum(f * centered**2, axis=1) * dv
    heat_flux = np.sum(f * centered**3, axis=1) * dv
    return {
        "rho": rho,
        "beta": beta,
        "P": pressure,
        "p": pressure,
        "Pi": np.zeros_like(pressure),
        "Q": heat_flux,
    }


def solve_periodic_poisson_1d(
    effective_density: np.ndarray,
    box_size: float,
    gravitational_constant: float = 1.0,
    subtract_mean: bool = True,
) -> np.ndarray:
    """Solve `d2 Phi/dx2 = 4*pi*G*rho_eff` on a periodic 1D box."""

    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    density = np.asarray(effective_density, dtype=float)
    if density.ndim != 1:
        raise ValueError("effective_density must be one-dimensional.")
    source = density - np.mean(density) if subtract_mean else density
    k = 2.0 * np.pi * np.fft.fftfreq(density.size, d=box_size / density.size)
    source_hat = np.fft.fft(4.0 * np.pi * gravitational_constant * source)
    potential_hat = np.zeros_like(source_hat, dtype=complex)
    nonzero = k**2 > 0.0
    potential_hat[nonzero] = -source_hat[nonzero] / (k[nonzero] ** 2)
    return np.real(np.fft.ifft(potential_hat))


def acceleration_from_potential_1d(potential: np.ndarray, box_size: float) -> np.ndarray:
    """Return diagnostic acceleration `-d Phi/dx` on a periodic 1D box."""

    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    phi = np.asarray(potential, dtype=float)
    if phi.ndim != 1:
        raise ValueError("potential must be one-dimensional.")
    k = 2.0 * np.pi * np.fft.fftfreq(phi.size, d=box_size / phi.size)
    return np.real(np.fft.ifft(-1j * k * np.fft.fft(phi)))


def two_sector_vlasov_poisson_accelerations(
    positive_distribution: np.ndarray,
    negative_distribution: np.ndarray,
    velocities: np.ndarray,
    dv: float,
    box_size: float,
    gravitational_constant: float = 1.0,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return plus/minus accelerations from a diagnostic two-sector effective density."""

    plus = np.asarray(positive_distribution, dtype=float)
    minus = np.asarray(negative_distribution, dtype=float)
    if plus.shape != minus.shape:
        raise ValueError("sector distributions must have the same shape.")
    rho_plus = velocity_moments(plus, velocities, dv)["rho"]
    rho_minus = velocity_moments(minus, velocities, dv)["rho"]
    effective_density = rho_plus - rho_minus
    potential_plus = solve_periodic_poisson_1d(
        effective_density,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    acceleration_plus = acceleration_from_potential_1d(potential_plus, box_size=box_size)
    return acceleration_plus, -acceleration_plus, effective_density


def two_sector_vlasov_poisson_step(
    positive_distribution: np.ndarray,
    negative_distribution: np.ndarray,
    velocities: np.ndarray,
    dt: float,
    dx: float,
    dv: float,
    box_size: float,
    gravitational_constant: float = 1.0,
) -> dict[str, np.ndarray]:
    """One self-consistent diagnostic two-sector Vlasov-Poisson step."""

    a_plus, a_minus, effective_density = two_sector_vlasov_poisson_accelerations(
        positive_distribution,
        negative_distribution,
        velocities,
        dv,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    return {
        "positive": strang_step_periodic(positive_distribution, velocities, a_plus, dt, dx, dv),
        "negative": strang_step_periodic(negative_distribution, velocities, a_minus, dt, dx, dv),
        "acceleration_positive": a_plus,
        "acceleration_negative": a_minus,
        "effective_density": effective_density,
    }


def phase_space_mass_with_weight(
    distribution: np.ndarray,
    dx: float,
    dv: float,
    spatial_weight: np.ndarray | float = 1.0,
) -> float:
    """Diagnostic weighted phase-space mass using one explicit spatial measure factor."""

    f = np.asarray(distribution, dtype=float)
    weight = np.asarray(spatial_weight, dtype=float)
    if f.ndim != 2:
        raise ValueError("distribution must have shape (nx, nv).")
    if weight.shape not in [(), (f.shape[0],)]:
        raise ValueError("spatial_weight must be scalar or have shape (nx,).")
    if dx <= 0.0 or dv <= 0.0:
        raise ValueError("dx and dv must be positive.")
    return float(np.sum(f * weight.reshape((-1, 1)) if weight.ndim == 1 else f * weight) * dx * dv)


def lorentz_boost_1p1(rapidity: float) -> np.ndarray:
    """Return a 1+1 Lorentz boost matrix for eta=diag(-1,+1)."""

    c = float(np.cosh(rapidity))
    s = float(np.sinh(rapidity))
    return np.asarray([[c, s], [s, c]], dtype=float)


def lorentz_residual_1p1(matrix: np.ndarray) -> float:
    """Return max residual of `L.T eta L - eta` for eta=diag(-1,+1)."""

    l_matrix = np.asarray(matrix, dtype=float)
    if l_matrix.shape != (2, 2):
        raise ValueError("matrix must have shape (2, 2).")
    eta = np.asarray([[-1.0, 0.0], [0.0, 1.0]])
    return float(np.max(np.abs(l_matrix.T @ eta @ l_matrix - eta)))


def stress_energy_1p1(distribution: np.ndarray, velocities: np.ndarray, dv: float, mass: float = 1.0) -> np.ndarray:
    """Diagnostic 1+1 kinetic stress tensor `int p^a p^b f dv`."""

    if mass <= 0.0:
        raise ValueError("mass must be positive.")
    f = np.asarray(distribution, dtype=float)
    v = np.asarray(velocities, dtype=float)
    if f.ndim != 2:
        raise ValueError("distribution must have shape (nx, nv).")
    if v.shape != (f.shape[1],):
        raise ValueError("velocities must have shape (nv,).")
    p0 = np.sqrt(mass**2 + v**2)
    total_f = np.sum(f, axis=0)
    return np.asarray(
        [
            [np.sum(total_f * p0 * p0) * dv, np.sum(total_f * p0 * v) * dv],
            [np.sum(total_f * v * p0) * dv, np.sum(total_f * v * v) * dv],
        ],
        dtype=float,
    )


def transform_rank2_1p1(tensor: np.ndarray, matrix: np.ndarray) -> np.ndarray:
    """Transform a diagnostic contravariant rank-2 tensor with one same-L matrix."""

    t = np.asarray(tensor, dtype=float)
    l_matrix = np.asarray(matrix, dtype=float)
    if t.shape != (2, 2) or l_matrix.shape != (2, 2):
        raise ValueError("tensor and matrix must both have shape (2, 2).")
    return l_matrix @ t @ l_matrix.T


def minkowski_trace_1p1(tensor: np.ndarray) -> float:
    """Return eta_ab T^ab for eta=diag(-1,+1)."""

    t = np.asarray(tensor, dtype=float)
    if t.shape != (2, 2):
        raise ValueError("tensor must have shape (2, 2).")
    return float(-t[0, 0] + t[1, 1])


def total_mass(distribution: np.ndarray, dx: float, dv: float) -> float:
    if dx <= 0.0 or dv <= 0.0:
        raise ValueError("dx and dv must be positive.")
    return float(np.sum(np.asarray(distribution, dtype=float)) * dx * dv)


def gaussian_phase_space(
    x: np.ndarray,
    v: np.ndarray,
    x0: float,
    sigma_x: float,
    sigma_v: float,
    box_size: float,
) -> np.ndarray:
    """Periodic x Gaussian times velocity Gaussian for diagnostics."""

    x_grid, _ = _validate_uniform_grid(x, "x")
    v_grid, _ = _validate_uniform_grid(v, "v")
    if sigma_x <= 0.0 or sigma_v <= 0.0 or box_size <= 0.0:
        raise ValueError("sigmas and box_size must be positive.")
    dx_periodic = np.minimum(np.abs(x_grid - x0), box_size - np.abs(x_grid - x0))
    spatial = np.exp(-(dx_periodic**2) / (2.0 * sigma_x**2))
    velocity = np.exp(-(v_grid**2) / (2.0 * sigma_v**2))
    return spatial[:, None] * velocity[None, :]
