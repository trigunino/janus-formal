"""Minimal periodic particle-mesh helpers for the Janus weak-field limit."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

import numpy as np

from .poisson import (
    acceleration_from_potential_2d,
    effective_density_grid,
    solve_periodic_poisson_2d,
)
from .signed_sector import BodyState, Sector


@dataclass(frozen=True)
class ParticleMeshFields:
    positive_density_abs: np.ndarray
    negative_density_abs: np.ndarray
    potential_positive: np.ndarray
    potential_negative: np.ndarray
    acceleration_positive: tuple[np.ndarray, np.ndarray]
    acceleration_negative: tuple[np.ndarray, np.ndarray]


@dataclass(frozen=True)
class SegregationMetrics:
    positive_internal_distance: float
    negative_internal_distance: float
    cross_sector_distance: float
    segregation_ratio: float


def _validate_mesh(grid_shape: tuple[int, int], box_size: float) -> tuple[int, int]:
    if len(grid_shape) != 2:
        raise ValueError("grid_shape must be two-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny = grid_shape
    if nx <= 0 or ny <= 0:
        raise ValueError("grid dimensions must be positive.")
    return nx, ny


def wrap_periodic_position(position: np.ndarray, box_size: float) -> np.ndarray:
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    point = np.asarray(position, dtype=float)
    if point.shape != (2,):
        raise ValueError("position must be a two-dimensional vector.")
    return np.mod(point, box_size)


def periodic_displacement(first: np.ndarray, second: np.ndarray, box_size: float) -> np.ndarray:
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    first_point = wrap_periodic_position(first, box_size)
    second_point = wrap_periodic_position(second, box_size)
    return np.mod(second_point - first_point + 0.5 * box_size, box_size) - 0.5 * box_size


def periodic_distance(first: np.ndarray, second: np.ndarray, box_size: float) -> float:
    return float(np.linalg.norm(periodic_displacement(first, second, box_size)))


def _sector_positions(bodies: Sequence[BodyState], sector: Sector) -> list[np.ndarray]:
    return [np.asarray(body.position, dtype=float) for body in bodies if body.sector == sector]


def mean_pairwise_periodic_distance(
    positions: Sequence[np.ndarray],
    box_size: float,
) -> float:
    if len(positions) < 2:
        return 0.0
    total = 0.0
    count = 0
    for first_index, first in enumerate(positions):
        for second in positions[first_index + 1 :]:
            total += periodic_distance(first, second, box_size)
            count += 1
    return total / count


def mean_cross_sector_periodic_distance(
    bodies: Sequence[BodyState],
    box_size: float,
) -> float:
    positive = _sector_positions(bodies, Sector.POSITIVE)
    negative = _sector_positions(bodies, Sector.NEGATIVE)
    if not positive or not negative:
        return 0.0
    total = 0.0
    count = 0
    for first in positive:
        for second in negative:
            total += periodic_distance(first, second, box_size)
            count += 1
    return total / count


def segregation_metrics(
    bodies: Sequence[BodyState],
    box_size: float,
) -> SegregationMetrics:
    positive_internal = mean_pairwise_periodic_distance(
        _sector_positions(bodies, Sector.POSITIVE),
        box_size,
    )
    negative_internal = mean_pairwise_periodic_distance(
        _sector_positions(bodies, Sector.NEGATIVE),
        box_size,
    )
    cross = mean_cross_sector_periodic_distance(bodies, box_size)
    same = 0.5 * (positive_internal + negative_internal)
    ratio = float("inf") if same == 0.0 and cross > 0.0 else cross / same if same > 0.0 else 0.0
    return SegregationMetrics(
        positive_internal_distance=positive_internal,
        negative_internal_distance=negative_internal,
        cross_sector_distance=cross,
        segregation_ratio=ratio,
    )


def _cic_entries(
    position: np.ndarray,
    grid_shape: tuple[int, int],
    box_size: float,
) -> tuple[tuple[int, int, float], ...]:
    nx, ny = _validate_mesh(grid_shape, box_size)
    point = wrap_periodic_position(position, box_size)
    sx = point[0] / (box_size / nx) - 0.5
    sy = point[1] / (box_size / ny) - 0.5
    i0 = int(np.floor(sx))
    j0 = int(np.floor(sy))
    tx = sx - i0
    ty = sy - j0
    i1 = i0 + 1
    j1 = j0 + 1
    return (
        (i0 % nx, j0 % ny, (1.0 - tx) * (1.0 - ty)),
        (i1 % nx, j0 % ny, tx * (1.0 - ty)),
        (i0 % nx, j1 % ny, (1.0 - tx) * ty),
        (i1 % nx, j1 % ny, tx * ty),
    )


def deposit_cloud_in_cell(
    bodies: Sequence[BodyState],
    grid_shape: tuple[int, int],
    box_size: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Deposit absolute sector masses as cell-area densities."""

    nx, ny = _validate_mesh(grid_shape, box_size)
    positive = np.zeros((nx, ny), dtype=float)
    negative = np.zeros((nx, ny), dtype=float)
    cell_area = box_size * box_size / (nx * ny)
    for body in bodies:
        if body.mass_abs < 0.0:
            raise ValueError("body masses must be non-negative.")
        target = positive if body.sector == Sector.POSITIVE else negative
        for i, j, weight in _cic_entries(body.position, grid_shape, box_size):
            target[i, j] += body.mass_abs * weight / cell_area
    return positive, negative


def interpolate_cloud_in_cell(
    grid: np.ndarray,
    positions: Sequence[np.ndarray],
    box_size: float,
) -> np.ndarray:
    values = np.asarray(grid, dtype=float)
    if values.ndim != 2:
        raise ValueError("grid must be two-dimensional.")
    _validate_mesh(values.shape, box_size)
    interpolated = []
    for position in positions:
        total = 0.0
        for i, j, weight in _cic_entries(position, values.shape, box_size):
            total += weight * values[i, j]
        interpolated.append(total)
    return np.asarray(interpolated, dtype=float)


def particle_mesh_fields(
    bodies: Sequence[BodyState],
    grid_shape: tuple[int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
) -> ParticleMeshFields:
    positive_density, negative_density = deposit_cloud_in_cell(
        bodies,
        grid_shape=grid_shape,
        box_size=box_size,
    )
    rho_plus = effective_density_grid(positive_density, negative_density, Sector.POSITIVE)
    rho_minus = effective_density_grid(positive_density, negative_density, Sector.NEGATIVE)
    potential_positive = solve_periodic_poisson_2d(
        rho_plus,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    potential_negative = solve_periodic_poisson_2d(
        rho_minus,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    return ParticleMeshFields(
        positive_density_abs=positive_density,
        negative_density_abs=negative_density,
        potential_positive=potential_positive,
        potential_negative=potential_negative,
        acceleration_positive=acceleration_from_potential_2d(potential_positive, box_size),
        acceleration_negative=acceleration_from_potential_2d(potential_negative, box_size),
    )


def particle_mesh_accelerations(
    bodies: Sequence[BodyState],
    grid_shape: tuple[int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
) -> list[np.ndarray]:
    fields = particle_mesh_fields(
        bodies,
        grid_shape=grid_shape,
        box_size=box_size,
        gravitational_constant=gravitational_constant,
    )
    accelerations: list[np.ndarray] = []
    for body in bodies:
        if np.asarray(body.velocity, dtype=float).shape != (2,):
            raise ValueError("velocity must be a two-dimensional vector.")
        if body.sector == Sector.POSITIVE:
            ax_grid, ay_grid = fields.acceleration_positive
        elif body.sector == Sector.NEGATIVE:
            ax_grid, ay_grid = fields.acceleration_negative
        else:
            raise ValueError(f"Unsupported sector: {body.sector}")
        positions = [body.position]
        ax = interpolate_cloud_in_cell(ax_grid, positions, box_size)[0]
        ay = interpolate_cloud_in_cell(ay_grid, positions, box_size)[0]
        accelerations.append(np.asarray([ax, ay], dtype=float))
    return accelerations


def leapfrog_particle_mesh_step(
    bodies: Sequence[BodyState],
    dt: float,
    grid_shape: tuple[int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
) -> list[BodyState]:
    if dt < 0.0:
        raise ValueError("dt must be non-negative.")
    accelerations = particle_mesh_accelerations(
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
            position=wrap_periodic_position(
                np.asarray(body.position, dtype=float) + dt * half_velocity,
                box_size,
            ),
            velocity=half_velocity,
            mass_abs=body.mass_abs,
            sector=body.sector,
        )
        for body, half_velocity in zip(bodies, half_velocities)
    ]
    new_accelerations = particle_mesh_accelerations(
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
