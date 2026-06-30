"""Prototype 3D comoving particle-mesh wrapper for Janus diagnostics."""

from __future__ import annotations

from collections.abc import Sequence

import numpy as np

from .particle_mesh_3d import particle_mesh_accelerations_3d, wrap_periodic_position_3d
from .signed_sector import BodyState


def cosmological_pm_step_3d(
    bodies: Sequence[BodyState],
    dt: float,
    scale_factor: float,
    expansion_rate: float,
    grid_shape: tuple[int, int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
    gravity_scale: float = 1.0,
    hubble_drag: float = 2.0,
) -> list[BodyState]:
    """One dimensionless 3D comoving PM step with Hubble drag."""

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

    force_factor = gravity_scale / scale_factor**3
    drag_half = float(np.exp(-0.5 * hubble_drag * expansion_rate * dt))
    accelerations = [
        force_factor * acceleration
        for acceleration in particle_mesh_accelerations_3d(
            bodies,
            grid_shape=grid_shape,
            box_size=box_size,
            gravitational_constant=gravitational_constant,
        )
    ]
    half_velocities = [
        drag_half * np.asarray(body.velocity, dtype=float) + 0.5 * dt * acceleration
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
    new_accelerations = [
        force_factor * acceleration
        for acceleration in particle_mesh_accelerations_3d(
            moved,
            grid_shape=grid_shape,
            box_size=box_size,
            gravitational_constant=gravitational_constant,
        )
    ]
    return [
        BodyState(
            position=moved_body.position,
            velocity=drag_half * (moved_body.velocity + 0.5 * dt * acceleration),
            mass_abs=moved_body.mass_abs,
            sector=moved_body.sector,
        )
        for moved_body, acceleration in zip(moved, new_accelerations)
    ]


def run_cosmological_pm_3d(
    bodies: Sequence[BodyState],
    dt: float,
    scale_factors: Sequence[float],
    expansion_rates: Sequence[float],
    grid_shape: tuple[int, int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
    gravity_scale: float = 1.0,
    hubble_drag: float = 2.0,
) -> list[list[BodyState]]:
    if len(scale_factors) != len(expansion_rates):
        raise ValueError("scale_factors and expansion_rates must have the same length.")
    if len(scale_factors) < 2:
        raise ValueError("at least two scale factors are required.")

    history = [list(bodies)]
    current = list(bodies)
    for scale_factor, expansion_rate in zip(scale_factors[:-1], expansion_rates[:-1]):
        current = cosmological_pm_step_3d(
            current,
            dt=dt,
            scale_factor=float(scale_factor),
            expansion_rate=float(expansion_rate),
            grid_shape=grid_shape,
            box_size=box_size,
            gravitational_constant=gravitational_constant,
            gravity_scale=gravity_scale,
            hubble_drag=hubble_drag,
        )
        history.append(current)
    return history
