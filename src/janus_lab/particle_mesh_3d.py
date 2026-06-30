"""Minimal periodic 3D particle-mesh helpers for Janus weak-field diagnostics."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

import numpy as np

from .poisson import (
    acceleration_from_potential_3d,
    effective_density_grid,
    solve_periodic_poisson_3d,
)
from .signed_sector import BodyState, Sector


@dataclass(frozen=True)
class ParticleMeshFields3D:
    positive_density_abs: np.ndarray
    negative_density_abs: np.ndarray
    potential_positive: np.ndarray
    potential_negative: np.ndarray
    acceleration_positive: tuple[np.ndarray, np.ndarray, np.ndarray]
    acceleration_negative: tuple[np.ndarray, np.ndarray, np.ndarray]


def _validate_mesh_3d(grid_shape: tuple[int, int, int], box_size: float) -> tuple[int, int, int]:
    if len(grid_shape) != 3:
        raise ValueError("grid_shape must be three-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny, nz = grid_shape
    if nx <= 0 or ny <= 0 or nz <= 0:
        raise ValueError("grid dimensions must be positive.")
    return nx, ny, nz


def wrap_periodic_position_3d(position: np.ndarray, box_size: float) -> np.ndarray:
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    point = np.asarray(position, dtype=float)
    if point.shape != (3,):
        raise ValueError("position must be a three-dimensional vector.")
    return np.mod(point, box_size)


def _cic_entries_3d(
    position: np.ndarray,
    grid_shape: tuple[int, int, int],
    box_size: float,
) -> tuple[tuple[int, int, int, float], ...]:
    nx, ny, nz = _validate_mesh_3d(grid_shape, box_size)
    point = wrap_periodic_position_3d(position, box_size)
    sx = point[0] / (box_size / nx) - 0.5
    sy = point[1] / (box_size / ny) - 0.5
    sz = point[2] / (box_size / nz) - 0.5
    i0 = int(np.floor(sx))
    j0 = int(np.floor(sy))
    k0 = int(np.floor(sz))
    tx = sx - i0
    ty = sy - j0
    tz = sz - k0
    entries = []
    for di, wx in ((0, 1.0 - tx), (1, tx)):
        for dj, wy in ((0, 1.0 - ty), (1, ty)):
            for dk, wz in ((0, 1.0 - tz), (1, tz)):
                entries.append(((i0 + di) % nx, (j0 + dj) % ny, (k0 + dk) % nz, wx * wy * wz))
    return tuple(entries)


def deposit_cloud_in_cell_3d(
    bodies: Sequence[BodyState],
    grid_shape: tuple[int, int, int],
    box_size: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Deposit absolute sector masses as cell-volume densities."""

    nx, ny, nz = _validate_mesh_3d(grid_shape, box_size)
    positive = np.zeros((nx, ny, nz), dtype=float)
    negative = np.zeros((nx, ny, nz), dtype=float)
    cell_volume = box_size**3 / (nx * ny * nz)
    for body in bodies:
        if body.mass_abs < 0.0:
            raise ValueError("body masses must be non-negative.")
        target = positive if body.sector == Sector.POSITIVE else negative
        for i, j, k, weight in _cic_entries_3d(body.position, grid_shape, box_size):
            target[i, j, k] += body.mass_abs * weight / cell_volume
    return positive, negative


def interpolate_cloud_in_cell_3d(
    grid: np.ndarray,
    positions: Sequence[np.ndarray],
    box_size: float,
) -> np.ndarray:
    values = np.asarray(grid, dtype=float)
    if values.ndim != 3:
        raise ValueError("grid must be three-dimensional.")
    _validate_mesh_3d(values.shape, box_size)
    interpolated = []
    for position in positions:
        total = 0.0
        for i, j, k, weight in _cic_entries_3d(position, values.shape, box_size):
            total += weight * values[i, j, k]
        interpolated.append(total)
    return np.asarray(interpolated, dtype=float)


def particle_mesh_fields_3d(
    bodies: Sequence[BodyState],
    grid_shape: tuple[int, int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
) -> ParticleMeshFields3D:
    positive_density, negative_density = deposit_cloud_in_cell_3d(
        bodies,
        grid_shape=grid_shape,
        box_size=box_size,
    )
    rho_plus = effective_density_grid(positive_density, negative_density, Sector.POSITIVE)
    rho_minus = effective_density_grid(positive_density, negative_density, Sector.NEGATIVE)
    potential_positive = solve_periodic_poisson_3d(
        rho_plus,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    potential_negative = solve_periodic_poisson_3d(
        rho_minus,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    return ParticleMeshFields3D(
        positive_density_abs=positive_density,
        negative_density_abs=negative_density,
        potential_positive=potential_positive,
        potential_negative=potential_negative,
        acceleration_positive=acceleration_from_potential_3d(potential_positive, box_size),
        acceleration_negative=acceleration_from_potential_3d(potential_negative, box_size),
    )


def particle_mesh_accelerations_3d(
    bodies: Sequence[BodyState],
    grid_shape: tuple[int, int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
) -> list[np.ndarray]:
    fields = particle_mesh_fields_3d(
        bodies,
        grid_shape=grid_shape,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    accelerations: list[np.ndarray] = []
    for body in bodies:
        if np.asarray(body.velocity, dtype=float).shape != (3,):
            raise ValueError("velocity must be a three-dimensional vector.")
        if body.sector == Sector.POSITIVE:
            ax_grid, ay_grid, az_grid = fields.acceleration_positive
        elif body.sector == Sector.NEGATIVE:
            ax_grid, ay_grid, az_grid = fields.acceleration_negative
        else:
            raise ValueError(f"Unsupported sector: {body.sector}")
        positions = [body.position]
        ax = interpolate_cloud_in_cell_3d(ax_grid, positions, box_size)[0]
        ay = interpolate_cloud_in_cell_3d(ay_grid, positions, box_size)[0]
        az = interpolate_cloud_in_cell_3d(az_grid, positions, box_size)[0]
        accelerations.append(np.asarray([ax, ay, az], dtype=float))
    return accelerations


def leapfrog_particle_mesh_step_3d(
    bodies: Sequence[BodyState],
    dt: float,
    grid_shape: tuple[int, int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
) -> list[BodyState]:
    if dt < 0.0:
        raise ValueError("dt must be non-negative.")
    accelerations = particle_mesh_accelerations_3d(
        bodies,
        grid_shape=grid_shape,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    half_velocities = [
        np.asarray(body.velocity, dtype=float) + 0.5 * dt * acceleration
        for body, acceleration in zip(bodies, accelerations)
    ]
    moved = [
        BodyState(
            position=wrap_periodic_position_3d(
                np.asarray(body.position, dtype=float) + dt * half_velocity,
                box_size,
            ),
            velocity=half_velocity,
            mass_abs=body.mass_abs,
            sector=body.sector,
        )
        for body, half_velocity in zip(bodies, half_velocities)
    ]
    new_accelerations = particle_mesh_accelerations_3d(
        moved,
        grid_shape=grid_shape,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    return [
        BodyState(
            position=moved_body.position,
            velocity=moved_body.velocity + 0.5 * dt * acceleration,
            mass_abs=moved_body.mass_abs,
            sector=moved_body.sector,
        )
        for moved_body, acceleration in zip(moved, new_accelerations)
    ]
