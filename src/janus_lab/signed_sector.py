"""Minimal Janus two-sector Newtonian-limit helpers.

This module implements only the source-verified interaction signs:
same sectors attract, opposite sectors repel. It is not a tensor solver.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

import numpy as np

from .models import ArrayLike, _as_array


class Sector(Enum):
    POSITIVE = "positive"
    NEGATIVE = "negative"


class NewtonianInteraction(Enum):
    ATTRACT = "attract"
    REPEL = "repel"


SECTOR_ORDER = (Sector.POSITIVE, Sector.NEGATIVE)


@dataclass(frozen=True)
class PointSource:
    position: np.ndarray
    mass_abs: float
    sector: Sector


@dataclass(frozen=True)
class BodyState:
    position: np.ndarray
    velocity: np.ndarray
    mass_abs: float
    sector: Sector


def metric_sheet_for(sector: Sector) -> str:
    if sector == Sector.POSITIVE:
        return "g_plus"
    if sector == Sector.NEGATIVE:
        return "g_minus"
    raise ValueError(f"Unsupported sector: {sector}")


def density_sign(sector: Sector) -> float:
    """Matter tensor density sign from M15 Eq. 5."""

    if sector == Sector.POSITIVE:
        return 1.0
    if sector == Sector.NEGATIVE:
        return -1.0
    raise ValueError(f"Unsupported sector: {sector}")


def metric_equation_sign(sector: Sector) -> float:
    """Overall source sign in the metric equation followed by this sector."""

    if sector == Sector.POSITIVE:
        return 1.0
    if sector == Sector.NEGATIVE:
        return -1.0
    raise ValueError(f"Unsupported sector: {sector}")


def newtonian_coupling_sign(source_sector: Sector, test_sector: Sector) -> float:
    """Effective Newtonian source sign in the metric followed by `test_sector`."""

    return metric_equation_sign(test_sector) * density_sign(source_sector)


def newtonian_coupling_matrix() -> np.ndarray:
    """Rows are test metric sectors; columns are source density sectors."""

    return np.asarray(
        [
            [newtonian_coupling_sign(source, test) for source in SECTOR_ORDER]
            for test in SECTOR_ORDER
        ],
        dtype=float,
    )


def poisson_rhs_density(
    positive_density_abs: float,
    negative_density_abs: float,
    test_sector: Sector,
    gravitational_constant: float = 1.0,
) -> float:
    """Weak-field Poisson RHS `Delta Phi_test` from absolute sector densities."""

    if positive_density_abs < 0.0:
        raise ValueError("positive_density_abs must be non-negative.")
    if negative_density_abs < 0.0:
        raise ValueError("negative_density_abs must be non-negative.")
    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")

    source_density = {
        Sector.POSITIVE: positive_density_abs,
        Sector.NEGATIVE: negative_density_abs,
    }
    effective_density = sum(
        newtonian_coupling_sign(source_sector, test_sector) * density
        for source_sector, density in source_density.items()
    )
    return float(4.0 * np.pi * gravitational_constant * effective_density)


def janus_interaction(source_sector: Sector, test_sector: Sector) -> NewtonianInteraction:
    return (
        NewtonianInteraction.ATTRACT
        if newtonian_coupling_sign(source_sector, test_sector) > 0.0
        else NewtonianInteraction.REPEL
    )


def interaction_sign(source_sector: Sector, test_sector: Sector) -> float:
    """Return +1 for attraction toward source, -1 for repulsion away from it."""

    return newtonian_coupling_sign(source_sector, test_sector)


def point_source_acceleration(
    test_position: ArrayLike,
    source: PointSource,
    test_sector: Sector,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> np.ndarray:
    """Acceleration from one point source in the Janus Newtonian limit."""

    if source.mass_abs < 0.0:
        raise ValueError("source.mass_abs must be non-negative.")
    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    if softening < 0.0:
        raise ValueError("softening must be non-negative.")

    test = _as_array(test_position).astype(float)
    source_position = _as_array(source.position).astype(float)
    if test.shape != source_position.shape:
        raise ValueError("test_position and source.position must have the same shape.")
    if test.ndim != 1:
        raise ValueError("positions must be one-dimensional vectors.")

    displacement = source_position - test
    radius2 = float(np.dot(displacement, displacement) + softening**2)
    if radius2 == 0.0:
        raise ValueError("point-source acceleration is singular at zero distance.")
    radius3 = radius2 ** 1.5
    sign = interaction_sign(source.sector, test_sector)
    return sign * gravitational_constant * source.mass_abs * displacement / radius3


def point_source_potential(
    test_position: ArrayLike,
    source: PointSource,
    test_sector: Sector,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> float:
    """Potential whose negative gradient gives `point_source_acceleration`."""

    if source.mass_abs < 0.0:
        raise ValueError("source.mass_abs must be non-negative.")
    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    if softening < 0.0:
        raise ValueError("softening must be non-negative.")

    test = _as_array(test_position).astype(float)
    source_position = _as_array(source.position).astype(float)
    if test.shape != source_position.shape:
        raise ValueError("test_position and source.position must have the same shape.")
    if test.ndim != 1:
        raise ValueError("positions must be one-dimensional vectors.")

    displacement = source_position - test
    radius = float(np.sqrt(np.dot(displacement, displacement) + softening**2))
    if radius == 0.0:
        raise ValueError("point-source potential is singular at zero distance.")
    sign = interaction_sign(source.sector, test_sector)
    return float(-sign * gravitational_constant * source.mass_abs / radius)


def total_acceleration(
    test_position: ArrayLike,
    sources: list[PointSource],
    test_sector: Sector,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> np.ndarray:
    test = _as_array(test_position).astype(float)
    total = np.zeros_like(test, dtype=float)
    for source in sources:
        total += point_source_acceleration(
            test,
            source,
            test_sector,
            gravitational_constant=gravitational_constant,
            softening=softening,
        )
    return total


def pair_potential_energy(
    first: BodyState,
    second: BodyState,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> float:
    """Weak-field pair potential, negative for attraction and positive for repulsion."""

    if first.mass_abs < 0.0 or second.mass_abs < 0.0:
        raise ValueError("body masses must be non-negative.")
    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    if softening < 0.0:
        raise ValueError("softening must be non-negative.")

    first_position = _as_array(first.position).astype(float)
    second_position = _as_array(second.position).astype(float)
    if first_position.shape != second_position.shape:
        raise ValueError("body positions must have the same shape.")
    if first_position.ndim != 1:
        raise ValueError("positions must be one-dimensional vectors.")

    displacement = second_position - first_position
    radius = float(np.sqrt(np.dot(displacement, displacement) + softening**2))
    if radius == 0.0:
        raise ValueError("pair potential is singular at zero distance.")
    sign = interaction_sign(first.sector, second.sector)
    return float(-sign * gravitational_constant * first.mass_abs * second.mass_abs / radius)


def kinetic_energy(bodies: list[BodyState]) -> float:
    total = 0.0
    for body in bodies:
        if body.mass_abs < 0.0:
            raise ValueError("body masses must be non-negative.")
        velocity = _as_array(body.velocity).astype(float)
        if velocity.ndim != 1:
            raise ValueError("velocities must be one-dimensional vectors.")
        total += 0.5 * body.mass_abs * float(np.dot(velocity, velocity))
    return total


def potential_energy(
    bodies: list[BodyState],
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> float:
    total = 0.0
    for first_index, first in enumerate(bodies):
        for second in bodies[first_index + 1 :]:
            total += pair_potential_energy(
                first,
                second,
                gravitational_constant=gravitational_constant,
                softening=softening,
            )
    return total


def total_energy(
    bodies: list[BodyState],
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> float:
    return kinetic_energy(bodies) + potential_energy(
        bodies,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )


def accelerations_for_bodies(
    bodies: list[BodyState],
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> list[np.ndarray]:
    """Pairwise accelerations for a weak-field two-sector N-body state."""

    accelerations: list[np.ndarray] = []
    for index, body in enumerate(bodies):
        sources = [
            PointSource(other.position, other.mass_abs, other.sector)
            for other_index, other in enumerate(bodies)
            if other_index != index
        ]
        accelerations.append(
            total_acceleration(
                body.position,
                sources,
                body.sector,
                gravitational_constant=gravitational_constant,
                softening=softening,
            )
        )
    return accelerations


def leapfrog_step(
    bodies: list[BodyState],
    dt: float,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> list[BodyState]:
    """One velocity-Verlet/leapfrog step for the weak-field sector model."""

    if dt < 0.0:
        raise ValueError("dt must be non-negative.")
    accelerations = accelerations_for_bodies(
        bodies,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )
    half_velocities = [
        _as_array(body.velocity).astype(float) + 0.5 * dt * acceleration
        for body, acceleration in zip(bodies, accelerations)
    ]
    moved = [
        BodyState(
            position=_as_array(body.position).astype(float) + dt * half_velocity,
            velocity=half_velocity,
            mass_abs=body.mass_abs,
            sector=body.sector,
        )
        for body, half_velocity in zip(bodies, half_velocities)
    ]
    new_accelerations = accelerations_for_bodies(
        moved,
        gravitational_constant=gravitational_constant,
        softening=softening,
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
