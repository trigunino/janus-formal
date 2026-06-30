"""Prototype comoving particle-mesh wrapper for Janus weak-field diagnostics."""

from __future__ import annotations

from collections.abc import Sequence

import numpy as np

from .particle_mesh import particle_mesh_accelerations, wrap_periodic_position
from .signed_sector import BodyState


def scale_factor_sequence(
    start_scale_factor: float,
    end_scale_factor: float,
    steps: int,
) -> np.ndarray:
    if start_scale_factor <= 0.0 or end_scale_factor <= 0.0:
        raise ValueError("scale factors must be positive.")
    if steps <= 0:
        raise ValueError("steps must be positive.")
    if end_scale_factor < start_scale_factor:
        raise ValueError("end_scale_factor must be >= start_scale_factor.")
    return np.linspace(start_scale_factor, end_scale_factor, steps + 1)


def cosmological_pm_step(
    bodies: Sequence[BodyState],
    dt: float,
    scale_factor: float,
    expansion_rate: float,
    grid_shape: tuple[int, int],
    box_size: float,
    gravitational_constant: float = 1.0,
    gravity_scale: float = 1.0,
    hubble_drag: float = 2.0,
) -> list[BodyState]:
    """One dimensionless comoving PM step with Hubble drag.

    This is a prototype numerical wrapper, not a precision cosmology integrator.
    """

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
        for acceleration in particle_mesh_accelerations(
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
    new_accelerations = [
        force_factor * acceleration
        for acceleration in particle_mesh_accelerations(
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


def run_cosmological_pm(
    bodies: Sequence[BodyState],
    dt: float,
    scale_factors: Sequence[float],
    expansion_rates: Sequence[float],
    grid_shape: tuple[int, int],
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
        current = cosmological_pm_step(
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
