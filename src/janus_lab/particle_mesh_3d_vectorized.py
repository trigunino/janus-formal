"""Vectorized 3D particle-mesh backend for larger Janus PM diagnostics."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .particle_mesh_3d import ParticleMeshFields3D
from .signed_sector import BodyState, Sector


@dataclass
class VectorizedParticleMeshState3D:
    positions: np.ndarray
    velocities: np.ndarray
    sector_signs: np.ndarray
    mass_abs: np.ndarray

    def __post_init__(self) -> None:
        self.positions = np.asarray(self.positions, dtype=float)
        self.velocities = np.asarray(self.velocities, dtype=float)
        self.sector_signs = np.asarray(self.sector_signs, dtype=np.int8)
        self.mass_abs = np.asarray(self.mass_abs, dtype=float)
        if self.positions.ndim != 2 or self.positions.shape[1] != 3:
            raise ValueError("positions must have shape (n, 3).")
        if self.velocities.shape != self.positions.shape:
            raise ValueError("velocities must have the same shape as positions.")
        if self.sector_signs.shape != (len(self.positions),):
            raise ValueError("sector_signs must have shape (n,).")
        if self.mass_abs.shape != (len(self.positions),):
            raise ValueError("mass_abs must have shape (n,).")
        if np.any(self.mass_abs < 0.0):
            raise ValueError("mass_abs values must be non-negative.")
        if np.any((self.sector_signs != 1) & (self.sector_signs != -1)):
            raise ValueError("sector_signs must be +1 or -1.")

    def copy(self) -> "VectorizedParticleMeshState3D":
        return VectorizedParticleMeshState3D(
            self.positions.copy(),
            self.velocities.copy(),
            self.sector_signs.copy(),
            self.mass_abs.copy(),
        )


def _validate_grid(grid_shape: tuple[int, int, int], box_size: float) -> tuple[int, int, int]:
    if len(grid_shape) != 3:
        raise ValueError("grid_shape must be three-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny, nz = grid_shape
    if nx <= 0 or ny <= 0 or nz <= 0:
        raise ValueError("grid dimensions must be positive.")
    return nx, ny, nz


def vectorized_state_from_bodies(bodies: list[BodyState]) -> VectorizedParticleMeshState3D:
    positions = np.asarray([body.position for body in bodies], dtype=float)
    velocities = np.asarray([body.velocity for body in bodies], dtype=float)
    sector_signs = np.asarray(
        [1 if body.sector == Sector.POSITIVE else -1 for body in bodies],
        dtype=np.int8,
    )
    mass_abs = np.asarray([body.mass_abs for body in bodies], dtype=float)
    return VectorizedParticleMeshState3D(positions, velocities, sector_signs, mass_abs)


def create_two_sector_lattice_state_3d(
    grid_shape: tuple[int, int, int],
    box_size: float,
    mass_abs: float = 1.0,
) -> VectorizedParticleMeshState3D:
    nx, ny, nz = _validate_grid(grid_shape, box_size)
    if mass_abs < 0.0:
        raise ValueError("mass_abs must be non-negative.")
    count = nx * ny * nz
    x = (np.arange(nx, dtype=float) + 0.5) * box_size / nx
    y = (np.arange(ny, dtype=float) + 0.5) * box_size / ny
    z = (np.arange(nz, dtype=float) + 0.5) * box_size / nz
    positions = np.empty((2 * count, 3), dtype=float)
    positions[:count, 0] = np.repeat(x, ny * nz)
    positions[:count, 1] = np.tile(np.repeat(y, nz), nx)
    positions[:count, 2] = np.tile(z, nx * ny)
    positions[count:] = positions[:count]
    velocities = np.zeros_like(positions)
    sector_signs = np.empty(2 * count, dtype=np.int8)
    sector_signs[:count] = 1
    sector_signs[count:] = -1
    masses = np.full(2 * count, mass_abs, dtype=float)
    return VectorizedParticleMeshState3D(positions, velocities, sector_signs, masses)


def create_two_sector_lattice_state_from_displacements_3d(
    positive_displacement: np.ndarray,
    negative_displacement: np.ndarray,
    box_size: float,
    mass_abs: float = 1.0,
) -> VectorizedParticleMeshState3D:
    positive = np.asarray(positive_displacement, dtype=float)
    negative = np.asarray(negative_displacement, dtype=float)
    if positive.shape != negative.shape:
        raise ValueError("sector displacements must have the same shape.")
    if positive.ndim != 4 or positive.shape[3] != 3:
        raise ValueError("displacements must have shape (nx, ny, nz, 3).")
    state = create_two_sector_lattice_state_3d(
        positive.shape[:3],
        box_size=box_size,
        mass_abs=mass_abs,
    )
    count = positive.shape[0] * positive.shape[1] * positive.shape[2]
    state.positions[:count] = np.mod(state.positions[:count] + positive.reshape(count, 3), box_size)
    state.positions[count:] = np.mod(state.positions[count:] + negative.reshape(count, 3), box_size)
    return state


def _cic_base(
    positions: np.ndarray,
    grid_shape: tuple[int, int, int],
    box_size: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    nx, ny, nz = grid_shape
    wrapped = np.mod(positions, box_size)
    scaled = wrapped / np.asarray([box_size / nx, box_size / ny, box_size / nz]) - 0.5
    base = np.floor(scaled).astype(np.int64)
    frac = scaled - base
    return base[:, 0], base[:, 1], base[:, 2], frac[:, 0], frac[:, 1], frac[:, 2]


def _deposit_chunk(
    density: np.ndarray,
    positions: np.ndarray,
    weights: np.ndarray,
    grid_shape: tuple[int, int, int],
    box_size: float,
) -> None:
    if len(positions) == 0:
        return
    nx, ny, nz = grid_shape
    flat = density.ravel()
    i0, j0, k0, tx, ty, tz = _cic_base(positions, grid_shape, box_size)
    for di, wx in ((0, 1.0 - tx), (1, tx)):
        ii = (i0 + di) % nx
        for dj, wy in ((0, 1.0 - ty), (1, ty)):
            jj = (j0 + dj) % ny
            for dk, wz in ((0, 1.0 - tz), (1, tz)):
                kk = (k0 + dk) % nz
                flat_index = (ii * ny + jj) * nz + kk
                flat += np.bincount(
                    flat_index,
                    weights=weights * wx * wy * wz,
                    minlength=flat.size,
                )


def deposit_cloud_in_cell_3d_vectorized(
    state: VectorizedParticleMeshState3D,
    grid_shape: tuple[int, int, int],
    box_size: float,
    chunk_size: int = 200_000,
) -> tuple[np.ndarray, np.ndarray]:
    nx, ny, nz = _validate_grid(grid_shape, box_size)
    positive = np.zeros((nx, ny, nz), dtype=float)
    negative = np.zeros((nx, ny, nz), dtype=float)
    cell_volume = box_size**3 / (nx * ny * nz)
    for start in range(0, len(state.positions), chunk_size):
        stop = min(start + chunk_size, len(state.positions))
        sector = state.sector_signs[start:stop]
        weights = state.mass_abs[start:stop] / cell_volume
        positions = state.positions[start:stop]
        positive_mask = sector == 1
        negative_mask = sector == -1
        _deposit_chunk(
            positive,
            positions[positive_mask],
            weights[positive_mask],
            grid_shape,
            box_size,
        )
        _deposit_chunk(
            negative,
            positions[negative_mask],
            weights[negative_mask],
            grid_shape,
            box_size,
        )
    return positive, negative


def deposit_sector_cloud_in_cell_3d_vectorized(
    state: VectorizedParticleMeshState3D,
    sector_sign: int,
    grid_shape: tuple[int, int, int],
    box_size: float,
    *,
    particle_weight_factor: np.ndarray | None = None,
    chunk_size: int = 200_000,
) -> np.ndarray:
    nx, ny, nz = _validate_grid(grid_shape, box_size)
    if sector_sign not in (1, -1):
        raise ValueError("sector_sign must be +1 or -1.")
    if particle_weight_factor is None:
        factors = np.ones(len(state.positions), dtype=float)
    else:
        factors = np.asarray(particle_weight_factor, dtype=float)
        if factors.shape != (len(state.positions),):
            raise ValueError("particle_weight_factor must have shape (n,).")
        if np.any(factors < 0.0):
            raise ValueError("particle_weight_factor values must be non-negative.")
    density = np.zeros((nx, ny, nz), dtype=float)
    cell_volume = box_size**3 / (nx * ny * nz)
    for start in range(0, len(state.positions), chunk_size):
        stop = min(start + chunk_size, len(state.positions))
        mask = state.sector_signs[start:stop] == sector_sign
        weights = state.mass_abs[start:stop] * factors[start:stop] / cell_volume
        _deposit_chunk(
            density,
            state.positions[start:stop][mask],
            weights[mask],
            grid_shape,
            box_size,
        )
    return density


def interpolate_cloud_in_cell_3d_vectorized(
    grid: np.ndarray,
    positions: np.ndarray,
    box_size: float,
    chunk_size: int = 200_000,
) -> np.ndarray:
    values = np.asarray(grid, dtype=float)
    if values.ndim != 3:
        raise ValueError("grid must be three-dimensional.")
    nx, ny, nz = _validate_grid(values.shape, box_size)
    result = np.empty(len(positions), dtype=float)
    flat = values.ravel()
    for start in range(0, len(positions), chunk_size):
        stop = min(start + chunk_size, len(positions))
        chunk = np.asarray(positions[start:stop], dtype=float)
        i0, j0, k0, tx, ty, tz = _cic_base(chunk, values.shape, box_size)
        total = np.zeros(len(chunk), dtype=float)
        for di, wx in ((0, 1.0 - tx), (1, tx)):
            ii = (i0 + di) % nx
            for dj, wy in ((0, 1.0 - ty), (1, ty)):
                jj = (j0 + dj) % ny
                for dk, wz in ((0, 1.0 - tz), (1, tz)):
                    kk = (k0 + dk) % nz
                    flat_index = (ii * ny + jj) * nz + kk
                    total += wx * wy * wz * flat[flat_index]
        result[start:stop] = total
    return result


def interpolate_vector_cloud_in_cell_3d_vectorized(
    grids: tuple[np.ndarray, np.ndarray, np.ndarray],
    positions: np.ndarray,
    box_size: float,
    chunk_size: int = 200_000,
) -> np.ndarray:
    components = tuple(np.asarray(grid, dtype=float) for grid in grids)
    if any(component.ndim != 3 for component in components):
        raise ValueError("all grids must be three-dimensional.")
    if components[1].shape != components[0].shape or components[2].shape != components[0].shape:
        raise ValueError("all grids must have the same shape.")
    nx, ny, nz = _validate_grid(components[0].shape, box_size)
    result = np.empty((len(positions), 3), dtype=float)
    flats = tuple(component.ravel() for component in components)
    for start in range(0, len(positions), chunk_size):
        stop = min(start + chunk_size, len(positions))
        chunk = np.asarray(positions[start:stop], dtype=float)
        i0, j0, k0, tx, ty, tz = _cic_base(chunk, components[0].shape, box_size)
        total = np.zeros((len(chunk), 3), dtype=float)
        for di, wx in ((0, 1.0 - tx), (1, tx)):
            ii = (i0 + di) % nx
            for dj, wy in ((0, 1.0 - ty), (1, ty)):
                jj = (j0 + dj) % ny
                for dk, wz in ((0, 1.0 - tz), (1, tz)):
                    kk = (k0 + dk) % nz
                    flat_index = (ii * ny + jj) * nz + kk
                    weight = wx * wy * wz
                    total[:, 0] += weight * flats[0][flat_index]
                    total[:, 1] += weight * flats[1][flat_index]
                    total[:, 2] += weight * flats[2][flat_index]
        result[start:stop] = total
    return result


def _solve_periodic_poisson_3d_fast(
    effective_density: np.ndarray,
    box_size: float,
    gravitational_constant: float,
) -> np.ndarray:
    density = np.asarray(effective_density, dtype=float)
    nx, ny, nz = _validate_grid(density.shape, box_size)
    source = density - float(np.mean(density))
    source_hat = np.fft.fftn(4.0 * np.pi * gravitational_constant * source)
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kz = 2.0 * np.pi * np.fft.fftfreq(nz, d=box_size / nz)
    k2 = kx[:, None, None] ** 2 + ky[None, :, None] ** 2 + kz[None, None, :] ** 2
    potential_hat = np.zeros_like(source_hat, dtype=complex)
    np.divide(-source_hat, k2, out=potential_hat, where=k2 > 0.0)
    return np.real(np.fft.ifftn(potential_hat))


def _acceleration_from_potential_3d_fast(
    potential: np.ndarray,
    box_size: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    phi = np.asarray(potential, dtype=float)
    nx, ny, nz = _validate_grid(phi.shape, box_size)
    phi_hat = np.fft.fftn(phi)
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kz = 2.0 * np.pi * np.fft.fftfreq(nz, d=box_size / nz)
    ax = np.real(np.fft.ifftn(-1j * kx[:, None, None] * phi_hat))
    ay = np.real(np.fft.ifftn(-1j * ky[None, :, None] * phi_hat))
    az = np.real(np.fft.ifftn(-1j * kz[None, None, :] * phi_hat))
    return ax, ay, az


def _acceleration_from_effective_density_3d_fast(
    effective_density: np.ndarray,
    box_size: float,
    gravitational_constant: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    density = np.asarray(effective_density, dtype=float)
    nx, ny, nz = _validate_grid(density.shape, box_size)
    source = density - float(np.mean(density))
    source_hat = np.fft.fftn(4.0 * np.pi * gravitational_constant * source)
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kz = 2.0 * np.pi * np.fft.fftfreq(nz, d=box_size / nz)
    k2 = kx[:, None, None] ** 2 + ky[None, :, None] ** 2 + kz[None, None, :] ** 2
    source_over_k2 = np.zeros_like(source_hat, dtype=complex)
    np.divide(source_hat, k2, out=source_over_k2, where=k2 > 0.0)
    ax = np.real(np.fft.ifftn(1j * kx[:, None, None] * source_over_k2))
    ay = np.real(np.fft.ifftn(1j * ky[None, :, None] * source_over_k2))
    az = np.real(np.fft.ifftn(1j * kz[None, None, :] * source_over_k2))
    return ax, ay, az


def particle_mesh_fields_3d_vectorized(
    state: VectorizedParticleMeshState3D,
    grid_shape: tuple[int, int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
    chunk_size: int = 200_000,
) -> ParticleMeshFields3D:
    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    positive_density, negative_density = deposit_cloud_in_cell_3d_vectorized(
        state,
        grid_shape=grid_shape,
        box_size=box_size,
        chunk_size=chunk_size,
    )
    effective_positive = positive_density - negative_density
    potential_positive = _solve_periodic_poisson_3d_fast(
        effective_positive,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    acceleration_positive = _acceleration_from_potential_3d_fast(
        potential_positive,
        box_size=box_size,
    )
    return ParticleMeshFields3D(
        positive_density_abs=positive_density,
        negative_density_abs=negative_density,
        potential_positive=potential_positive,
        potential_negative=-potential_positive,
        acceleration_positive=acceleration_positive,
        acceleration_negative=tuple(-component for component in acceleration_positive),
    )


def particle_mesh_accelerations_3d_vectorized(
    state: VectorizedParticleMeshState3D,
    grid_shape: tuple[int, int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
    chunk_size: int = 200_000,
) -> np.ndarray:
    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    positive_density, negative_density = deposit_cloud_in_cell_3d_vectorized(
        state,
        grid_shape=grid_shape,
        box_size=box_size,
        chunk_size=chunk_size,
    )
    acceleration_positive = _acceleration_from_effective_density_3d_fast(
        positive_density - negative_density,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    accelerations = np.empty_like(state.positions)
    positive_mask = state.sector_signs == 1
    negative_mask = state.sector_signs == -1
    accelerations[positive_mask] = interpolate_vector_cloud_in_cell_3d_vectorized(
        acceleration_positive,
        state.positions[positive_mask],
        box_size=box_size,
        chunk_size=chunk_size,
    )
    accelerations[negative_mask] = -interpolate_vector_cloud_in_cell_3d_vectorized(
        acceleration_positive,
        state.positions[negative_mask],
        box_size=box_size,
        chunk_size=chunk_size,
    )
    return accelerations


def cosmological_pm_step_3d_vectorized(
    state: VectorizedParticleMeshState3D,
    dt: float,
    scale_factor: float,
    expansion_rate: float,
    grid_shape: tuple[int, int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
    gravity_scale: float = 1.0,
    hubble_drag: float = 2.0,
    chunk_size: int = 200_000,
    in_place: bool = False,
) -> VectorizedParticleMeshState3D:
    if dt < 0.0:
        raise ValueError("dt must be non-negative.")
    if scale_factor <= 0.0:
        raise ValueError("scale_factor must be positive.")
    if expansion_rate < 0.0:
        raise ValueError("expansion_rate must be non-negative.")
    if gravity_scale < 0.0:
        raise ValueError("gravity_scale must be non-negative.")
    if hubble_drag < 0.0:
        raise ValueError("hubble_drag must be non-negative.")
    updated = state if in_place else state.copy()
    force_factor = gravity_scale / scale_factor**3
    drag_half = float(np.exp(-0.5 * hubble_drag * expansion_rate * dt))
    accelerations = force_factor * particle_mesh_accelerations_3d_vectorized(
        updated,
        grid_shape=grid_shape,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
        chunk_size=chunk_size,
    )
    updated.velocities *= drag_half
    updated.velocities += 0.5 * dt * accelerations
    updated.positions = np.mod(updated.positions + dt * updated.velocities, box_size)
    new_accelerations = force_factor * particle_mesh_accelerations_3d_vectorized(
        updated,
        grid_shape=grid_shape,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
        chunk_size=chunk_size,
    )
    updated.velocities += 0.5 * dt * new_accelerations
    updated.velocities *= drag_half
    return updated


def estimate_vectorized_pm_memory_bytes(
    grid_shape: tuple[int, int, int],
    particle_count: int,
    mesh_work_arrays: int = 14,
) -> int:
    nx, ny, nz = _validate_grid(grid_shape, 1.0)
    if particle_count < 0:
        raise ValueError("particle_count must be non-negative.")
    cell_count = nx * ny * nz
    state_bytes = particle_count * (6 * 8 + 8 + 1)
    mesh_bytes = mesh_work_arrays * cell_count * 8
    return int(state_bytes + mesh_bytes)
