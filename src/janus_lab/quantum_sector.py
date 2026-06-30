"""Minimal nonrelativistic Janus two-sector quantum helpers.

The sector mass parameter stays positive in the Schrodinger kinetic term.
Janus signs enter through the bimetric gravitational potential.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

import numpy as np

from .models import ArrayLike, _as_array
from .signed_sector import PointSource, Sector, point_source_potential


def _validate_positive(name: str, value: float) -> None:
    if value <= 0.0:
        raise ValueError(f"{name} must be positive.")


class BoundaryCondition(Enum):
    DIRICHLET = "dirichlet"
    PERIODIC = "periodic"


def _boundary_condition(value: BoundaryCondition | str) -> BoundaryCondition:
    if isinstance(value, BoundaryCondition):
        return value
    try:
        return BoundaryCondition(value)
    except ValueError as exc:
        raise ValueError(f"Unsupported boundary condition: {value}") from exc


def _uniform_grid_spacing(grid: ArrayLike) -> tuple[np.ndarray, float]:
    x = _as_array(grid).astype(float)
    if x.ndim != 1:
        raise ValueError("grid must be a one-dimensional array.")
    if x.size < 3:
        raise ValueError("grid must contain at least three points.")

    spacing = np.diff(x)
    dx = float(spacing[0])
    if dx <= 0.0:
        raise ValueError("grid must be strictly increasing.")
    if not np.allclose(spacing, dx):
        raise ValueError("grid must be uniformly spaced.")
    return x, dx


@dataclass(frozen=True)
class JanusQuantumState1D:
    """Two independent sector wavefunctions on the same 1D grid."""

    grid: np.ndarray
    positive: np.ndarray
    negative: np.ndarray
    mass_abs: float
    hbar: float = 1.0

    def __post_init__(self) -> None:
        _validate_positive("mass_abs", self.mass_abs)
        _validate_positive("hbar", self.hbar)
        grid, _ = _uniform_grid_spacing(self.grid)
        positive = np.asarray(self.positive, dtype=complex)
        negative = np.asarray(self.negative, dtype=complex)
        if positive.shape != grid.shape or negative.shape != grid.shape:
            raise ValueError("sector wavefunctions must match grid shape.")

        object.__setattr__(self, "grid", grid.copy())
        object.__setattr__(self, "positive", positive.copy())
        object.__setattr__(self, "negative", negative.copy())


@dataclass(frozen=True)
class SchrodingerPoissonRun1D:
    final_state: JanusQuantumState1D
    energies: np.ndarray
    positive_probabilities: np.ndarray
    negative_probabilities: np.ndarray
    sector_separations: np.ndarray

    @property
    def energy_drift(self) -> float:
        return float(self.energies[-1] - self.energies[0])


@dataclass(frozen=True)
class JanusQuantumModel1D:
    """Self-contained Janus quantum model surface, kept separate from PM/Vlasov code."""

    grid: np.ndarray
    mass_abs: float
    sources: tuple[PointSource, ...] = ()
    hbar: float = 1.0
    gravitational_constant: float = 1.0
    softening: float = 0.0
    boundary_condition: BoundaryCondition = BoundaryCondition.DIRICHLET

    def __post_init__(self) -> None:
        _validate_positive("mass_abs", self.mass_abs)
        _validate_positive("hbar", self.hbar)
        if self.gravitational_constant < 0.0:
            raise ValueError("gravitational_constant must be non-negative.")
        if self.softening < 0.0:
            raise ValueError("softening must be non-negative.")
        grid, _ = _uniform_grid_spacing(self.grid)
        object.__setattr__(self, "grid", grid.copy())
        object.__setattr__(self, "sources", tuple(self.sources))
        object.__setattr__(self, "boundary_condition", _boundary_condition(self.boundary_condition))

    def state(self, positive: ArrayLike, negative: ArrayLike) -> JanusQuantumState1D:
        return JanusQuantumState1D(
            self.grid,
            np.asarray(positive, dtype=complex),
            np.asarray(negative, dtype=complex),
            self.mass_abs,
            hbar=self.hbar,
        )

    def _validate_state(self, state: JanusQuantumState1D) -> None:
        if state.grid.shape != self.grid.shape or not np.allclose(state.grid, self.grid):
            raise ValueError("state grid does not match model grid.")
        if state.mass_abs != self.mass_abs:
            raise ValueError("state mass_abs does not match model mass_abs.")
        if state.hbar != self.hbar:
            raise ValueError("state hbar does not match model hbar.")

    def normalize(self, state: JanusQuantumState1D) -> JanusQuantumState1D:
        self._validate_state(state)
        return normalize_janus_state_1d(state)

    def probability(self, state: JanusQuantumState1D) -> float:
        self._validate_state(state)
        return janus_state_probability_1d(state)

    def sector_hamiltonian(self, sector: Sector) -> np.ndarray:
        return janus_sector_hamiltonian_1d(
            self.grid,
            self.mass_abs,
            sector,
            list(self.sources),
            hbar=self.hbar,
            boundary_condition=self.boundary_condition,
            gravitational_constant=self.gravitational_constant,
            softening=self.softening,
        )

    def hamiltonian(self) -> np.ndarray:
        return janus_bimetric_hamiltonian_1d(
            self.grid,
            self.mass_abs,
            list(self.sources),
            hbar=self.hbar,
            boundary_condition=self.boundary_condition,
            gravitational_constant=self.gravitational_constant,
            softening=self.softening,
        )

    def energy(self, state: JanusQuantumState1D) -> float:
        self._validate_state(state)
        return janus_energy_expectation_1d(
            state,
            list(self.sources),
            boundary_condition=self.boundary_condition,
            gravitational_constant=self.gravitational_constant,
            softening=self.softening,
        )

    def evolve(self, state: JanusQuantumState1D, dt: float) -> JanusQuantumState1D:
        self._validate_state(state)
        return evolve_janus_state_1d(
            state,
            list(self.sources),
            dt,
            boundary_condition=self.boundary_condition,
            gravitational_constant=self.gravitational_constant,
            softening=self.softening,
        )

    def self_consistent_potentials(self, state: JanusQuantumState1D) -> tuple[np.ndarray, np.ndarray]:
        self._validate_state(state)
        return janus_schrodinger_poisson_potentials_1d(
            state,
            gravitational_constant=self.gravitational_constant,
        )

    def self_consistent_hamiltonians(self, state: JanusQuantumState1D) -> tuple[np.ndarray, np.ndarray]:
        self._validate_state(state)
        return janus_schrodinger_poisson_hamiltonians_1d(
            state,
            boundary_condition=self.boundary_condition,
            gravitational_constant=self.gravitational_constant,
        )

    def evolve_self_consistent(self, state: JanusQuantumState1D, dt: float) -> JanusQuantumState1D:
        self._validate_state(state)
        return schrodinger_poisson_step_1d(
            state,
            dt,
            boundary_condition=self.boundary_condition,
            gravitational_constant=self.gravitational_constant,
        )

    def self_consistent_energy(self, state: JanusQuantumState1D) -> float:
        self._validate_state(state)
        return schrodinger_poisson_energy_1d(
            state,
            boundary_condition=self.boundary_condition,
            gravitational_constant=self.gravitational_constant,
        )

    def run_self_consistent(self, state: JanusQuantumState1D, steps: int, dt: float) -> SchrodingerPoissonRun1D:
        self._validate_state(state)
        return run_schrodinger_poisson_1d(
            state,
            steps=steps,
            dt=dt,
            boundary_condition=self.boundary_condition,
            gravitational_constant=self.gravitational_constant,
        )


def finite_difference_laplacian_1d(
    grid: ArrayLike,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
) -> np.ndarray:
    """Second-derivative matrix on a uniform 1D grid."""

    x, dx = _uniform_grid_spacing(grid)
    boundary = _boundary_condition(boundary_condition)

    inv_dx2 = 1.0 / dx**2
    laplacian = np.zeros((x.size, x.size), dtype=float)
    np.fill_diagonal(laplacian, -2.0 * inv_dx2)
    indices = np.arange(x.size - 1)
    laplacian[indices, indices + 1] = inv_dx2
    laplacian[indices + 1, indices] = inv_dx2
    if boundary == BoundaryCondition.PERIODIC:
        laplacian[0, -1] = inv_dx2
        laplacian[-1, 0] = inv_dx2
    return laplacian


def kinetic_operator_1d(
    grid: ArrayLike,
    mass_abs: float,
    hbar: float = 1.0,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
) -> np.ndarray:
    """Return `-(hbar^2 / 2m) Delta`, identical for both Janus sectors."""

    _validate_positive("mass_abs", mass_abs)
    _validate_positive("hbar", hbar)
    return -(hbar**2 / (2.0 * mass_abs)) * finite_difference_laplacian_1d(
        grid,
        boundary_condition=boundary_condition,
    )


def momentum_operator_1d(
    grid: ArrayLike,
    hbar: float = 1.0,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
) -> np.ndarray:
    """Central-difference momentum operator `-i hbar d/dx`."""

    x, dx = _uniform_grid_spacing(grid)
    _validate_positive("hbar", hbar)
    boundary = _boundary_condition(boundary_condition)
    derivative = np.zeros((x.size, x.size), dtype=float)
    indices = np.arange(x.size - 1)
    derivative[indices, indices + 1] = 0.5 / dx
    derivative[indices + 1, indices] = -0.5 / dx
    if boundary == BoundaryCondition.PERIODIC:
        derivative[0, -1] = -0.5 / dx
        derivative[-1, 0] = 0.5 / dx
    return -1j * hbar * derivative


def position_operator_1d(grid: ArrayLike) -> np.ndarray:
    x, _ = _uniform_grid_spacing(grid)
    return np.diag(x)


def sector_probability_density_1d(wavefunction: ArrayLike) -> np.ndarray:
    """Return `|psi|^2` for one sector."""

    psi = np.asarray(wavefunction, dtype=complex)
    if psi.ndim != 1:
        raise ValueError("wavefunction must be a one-dimensional array.")
    return np.abs(psi) ** 2


def sector_probability_1d(grid: ArrayLike, wavefunction: ArrayLike) -> float:
    """Grid-integrated sector probability."""

    x, dx = _uniform_grid_spacing(grid)
    density = sector_probability_density_1d(wavefunction)
    if density.shape != x.shape:
        raise ValueError("wavefunction must match grid shape.")
    return float(np.sum(density) * dx)


def normalize_wavefunction_1d(grid: ArrayLike, wavefunction: ArrayLike) -> np.ndarray:
    probability = sector_probability_1d(grid, wavefunction)
    if probability <= 0.0:
        raise ValueError("wavefunction probability must be positive.")
    return np.asarray(wavefunction, dtype=complex) / np.sqrt(probability)


def gaussian_wavepacket_1d(
    grid: ArrayLike,
    center: float,
    width: float,
    momentum: float = 0.0,
    hbar: float = 1.0,
) -> np.ndarray:
    """Normalized Gaussian packet whose `width` is the position standard deviation."""

    _validate_positive("width", width)
    _validate_positive("hbar", hbar)
    x, _ = _uniform_grid_spacing(grid)
    envelope = np.exp(-((x - center) ** 2) / (4.0 * width**2))
    phase = np.exp(1j * momentum * (x - center) / hbar)
    return normalize_wavefunction_1d(x, envelope * phase)


def janus_state_probability_1d(state: JanusQuantumState1D) -> float:
    return sector_probability_1d(state.grid, state.positive) + sector_probability_1d(
        state.grid,
        state.negative,
    )


def quantum_mass_densities_1d(state: JanusQuantumState1D) -> tuple[np.ndarray, np.ndarray]:
    return (
        state.mass_abs * sector_probability_density_1d(state.positive),
        state.mass_abs * sector_probability_density_1d(state.negative),
    )


def normalize_janus_state_1d(state: JanusQuantumState1D) -> JanusQuantumState1D:
    probability = janus_state_probability_1d(state)
    if probability <= 0.0:
        raise ValueError("Janus state probability must be positive.")
    scale = np.sqrt(probability)
    return JanusQuantumState1D(
        state.grid,
        state.positive / scale,
        state.negative / scale,
        state.mass_abs,
        hbar=state.hbar,
    )


def potential_energy_from_sources_1d(
    grid: ArrayLike,
    test_mass_abs: float,
    test_sector: Sector,
    sources: list[PointSource],
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> np.ndarray:
    """Gravitational potential energy `m Phi_sector` on a 1D grid."""

    _validate_positive("test_mass_abs", test_mass_abs)
    x = _as_array(grid).astype(float)
    if x.ndim != 1:
        raise ValueError("grid must be a one-dimensional array.")

    values = np.zeros_like(x, dtype=float)
    for source in sources:
        for index, position in enumerate(x):
            values[index] += test_mass_abs * point_source_potential(
                np.asarray([position]),
                source,
                test_sector,
                gravitational_constant=gravitational_constant,
                softening=softening,
            )
    return values


def expectation_value_1d(
    grid: ArrayLike,
    wavefunction: ArrayLike,
    operator: ArrayLike,
) -> complex:
    x, dx = _uniform_grid_spacing(grid)
    psi = np.asarray(wavefunction, dtype=complex)
    op = np.asarray(operator, dtype=complex)
    if psi.shape != x.shape:
        raise ValueError("wavefunction must match grid shape.")
    if op.shape != (x.size, x.size):
        raise ValueError("operator must be a square matrix matching grid size.")
    return complex(np.vdot(psi, op @ psi) * dx)


def position_expectation_1d(grid: ArrayLike, wavefunction: ArrayLike) -> float:
    value = expectation_value_1d(grid, wavefunction, position_operator_1d(grid))
    if abs(value.imag) > 1e-10:
        raise ValueError("position expectation has a non-negligible imaginary part.")
    return float(value.real)


def sector_centroid_separation_1d(state: JanusQuantumState1D) -> float:
    positive_probability = sector_probability_1d(state.grid, state.positive)
    negative_probability = sector_probability_1d(state.grid, state.negative)
    if positive_probability <= 0.0 or negative_probability <= 0.0:
        raise ValueError("both sectors must have positive probability.")
    positive_center = position_expectation_1d(state.grid, state.positive) / positive_probability
    negative_center = position_expectation_1d(state.grid, state.negative) / negative_probability
    return float(abs(negative_center - positive_center))


def position_variance_1d(grid: ArrayLike, wavefunction: ArrayLike) -> float:
    x, _ = _uniform_grid_spacing(grid)
    mean = position_expectation_1d(x, wavefunction)
    value = expectation_value_1d(x, wavefunction, np.diag((x - mean) ** 2))
    if abs(value.imag) > 1e-10:
        raise ValueError("position variance has a non-negligible imaginary part.")
    return float(value.real)


def momentum_expectation_1d(
    grid: ArrayLike,
    wavefunction: ArrayLike,
    hbar: float = 1.0,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
) -> float:
    value = expectation_value_1d(
        grid,
        wavefunction,
        momentum_operator_1d(grid, hbar=hbar, boundary_condition=boundary_condition),
    )
    if abs(value.imag) > 1e-10:
        raise ValueError("momentum expectation has a non-negligible imaginary part.")
    return float(value.real)


def momentum_variance_1d(
    grid: ArrayLike,
    wavefunction: ArrayLike,
    hbar: float = 1.0,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
) -> float:
    x, _ = _uniform_grid_spacing(grid)
    momentum = momentum_operator_1d(x, hbar=hbar, boundary_condition=boundary_condition)
    mean = momentum_expectation_1d(
        x,
        wavefunction,
        hbar=hbar,
        boundary_condition=boundary_condition,
    )
    centered = momentum - mean * np.eye(x.size, dtype=complex)
    value = expectation_value_1d(x, wavefunction, centered @ centered)
    if abs(value.imag) > 1e-10:
        raise ValueError("momentum variance has a non-negligible imaginary part.")
    return float(value.real)


def probability_current_1d(
    grid: ArrayLike,
    wavefunction: ArrayLike,
    mass_abs: float,
    hbar: float = 1.0,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
) -> np.ndarray:
    """Return `hbar/m Im(conj(psi) dpsi/dx)`."""

    x, _ = _uniform_grid_spacing(grid)
    _validate_positive("mass_abs", mass_abs)
    _validate_positive("hbar", hbar)
    psi = np.asarray(wavefunction, dtype=complex)
    if psi.shape != x.shape:
        raise ValueError("wavefunction must match grid shape.")
    derivative = 1j * momentum_operator_1d(
        x,
        hbar=1.0,
        boundary_condition=boundary_condition,
    )
    return (hbar / mass_abs) * np.imag(np.conj(psi) * (derivative @ psi))


def harmonic_oscillator_potential_1d(
    grid: ArrayLike,
    mass_abs: float,
    omega: float,
    center: float = 0.0,
) -> np.ndarray:
    _validate_positive("mass_abs", mass_abs)
    _validate_positive("omega", omega)
    x, _ = _uniform_grid_spacing(grid)
    return 0.5 * mass_abs * omega**2 * (x - center) ** 2


def solve_periodic_poisson_1d(
    grid: ArrayLike,
    effective_density: ArrayLike,
    gravitational_constant: float = 1.0,
    subtract_mean: bool = True,
) -> np.ndarray:
    """Solve `d2 Phi/dx2 = 4*pi*G*rho_eff` on a periodic 1D grid."""

    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    x, dx = _uniform_grid_spacing(grid)
    density = _as_array(effective_density).astype(float)
    if density.shape != x.shape:
        raise ValueError("effective_density must match grid shape.")

    source = density - np.mean(density) if subtract_mean else density
    k = 2.0 * np.pi * np.fft.fftfreq(x.size, d=dx)
    source_hat = np.fft.fft(4.0 * np.pi * gravitational_constant * source)
    potential_hat = np.zeros_like(source_hat, dtype=complex)
    nonzero = k**2 > 0.0
    potential_hat[nonzero] = -source_hat[nonzero] / (k[nonzero] ** 2)
    return np.real(np.fft.ifft(potential_hat))


def janus_schrodinger_poisson_potentials_1d(
    state: JanusQuantumState1D,
    gravitational_constant: float = 1.0,
) -> tuple[np.ndarray, np.ndarray]:
    positive_density, negative_density = quantum_mass_densities_1d(state)
    phi_positive = solve_periodic_poisson_1d(
        state.grid,
        positive_density - negative_density,
        gravitational_constant=gravitational_constant,
    )
    return phi_positive, -phi_positive


def schrodinger_hamiltonian_1d(
    grid: ArrayLike,
    mass_abs: float,
    potential_energy: ArrayLike | None = None,
    hbar: float = 1.0,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
) -> np.ndarray:
    """Finite-difference Schrodinger Hamiltonian `T + V`."""

    kinetic = kinetic_operator_1d(
        grid,
        mass_abs,
        hbar=hbar,
        boundary_condition=boundary_condition,
    )
    if potential_energy is None:
        return kinetic

    potential = _as_array(potential_energy).astype(float)
    if potential.shape != (kinetic.shape[0],):
        raise ValueError("potential_energy must match grid shape.")
    return kinetic + np.diag(potential)


def janus_schrodinger_poisson_hamiltonians_1d(
    state: JanusQuantumState1D,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.PERIODIC,
    gravitational_constant: float = 1.0,
) -> tuple[np.ndarray, np.ndarray]:
    phi_positive, phi_negative = janus_schrodinger_poisson_potentials_1d(
        state,
        gravitational_constant=gravitational_constant,
    )
    positive = schrodinger_hamiltonian_1d(
        state.grid,
        state.mass_abs,
        potential_energy=state.mass_abs * phi_positive,
        hbar=state.hbar,
        boundary_condition=boundary_condition,
    )
    negative = schrodinger_hamiltonian_1d(
        state.grid,
        state.mass_abs,
        potential_energy=state.mass_abs * phi_negative,
        hbar=state.hbar,
        boundary_condition=boundary_condition,
    )
    return positive, negative


def schrodinger_poisson_energy_1d(
    state: JanusQuantumState1D,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.PERIODIC,
    gravitational_constant: float = 1.0,
) -> float:
    x, dx = _uniform_grid_spacing(state.grid)
    kinetic = kinetic_operator_1d(
        x,
        state.mass_abs,
        hbar=state.hbar,
        boundary_condition=boundary_condition,
    )
    kinetic_energy = expectation_value_1d(x, state.positive, kinetic)
    kinetic_energy += expectation_value_1d(x, state.negative, kinetic)
    rho_positive, rho_negative = quantum_mass_densities_1d(state)
    phi_positive, phi_negative = janus_schrodinger_poisson_potentials_1d(
        state,
        gravitational_constant=gravitational_constant,
    )
    potential_energy = 0.5 * np.sum(rho_positive * phi_positive + rho_negative * phi_negative) * dx
    energy = kinetic_energy + potential_energy
    if abs(energy.imag) > 1e-10:
        raise ValueError("Schrodinger-Poisson energy has a non-negligible imaginary part.")
    return float(energy.real)


def unitary_step_1d(
    wavefunction: ArrayLike,
    hamiltonian: ArrayLike,
    dt: float,
    hbar: float = 1.0,
) -> np.ndarray:
    """Exact finite-dimensional unitary step for a Hermitian Hamiltonian."""

    _validate_positive("hbar", hbar)
    psi = np.asarray(wavefunction, dtype=complex)
    hamiltonian_matrix = np.asarray(hamiltonian, dtype=complex)
    if psi.ndim != 1:
        raise ValueError("wavefunction must be a one-dimensional array.")
    if hamiltonian_matrix.shape != (psi.size, psi.size):
        raise ValueError("hamiltonian must be a square matrix matching wavefunction size.")
    if not np.allclose(hamiltonian_matrix, hamiltonian_matrix.conj().T):
        raise ValueError("hamiltonian must be Hermitian.")

    eigenvalues, eigenvectors = np.linalg.eigh(hamiltonian_matrix)
    amplitudes = eigenvectors.conj().T @ psi
    phases = np.exp(-1j * eigenvalues * dt / hbar)
    return eigenvectors @ (phases * amplitudes)


def janus_sector_hamiltonian_1d(
    grid: ArrayLike,
    test_mass_abs: float,
    test_sector: Sector,
    sources: list[PointSource],
    hbar: float = 1.0,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> np.ndarray:
    """Sector Hamiltonian with Janus same-sector attraction/cross-sector repulsion."""

    potential = potential_energy_from_sources_1d(
        grid,
        test_mass_abs,
        test_sector,
        sources,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )
    return schrodinger_hamiltonian_1d(
        grid,
        test_mass_abs,
        potential,
        hbar=hbar,
        boundary_condition=boundary_condition,
    )


def janus_bimetric_hamiltonian_1d(
    grid: ArrayLike,
    test_mass_abs: float,
    sources: list[PointSource],
    hbar: float = 1.0,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> np.ndarray:
    """Block-diagonal positive/negative sector Hamiltonian.

    Off-diagonal quantum mixing is intentionally absent in this minimal
    bimetric scaffold; sectors interact only through their gravitational
    source potentials.
    """

    positive = janus_sector_hamiltonian_1d(
        grid,
        test_mass_abs,
        Sector.POSITIVE,
        sources,
        hbar=hbar,
        boundary_condition=boundary_condition,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )
    negative = janus_sector_hamiltonian_1d(
        grid,
        test_mass_abs,
        Sector.NEGATIVE,
        sources,
        hbar=hbar,
        boundary_condition=boundary_condition,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )

    size = positive.shape[0]
    block = np.zeros((2 * size, 2 * size), dtype=float)
    block[:size, :size] = positive
    block[size:, size:] = negative
    return block


def janus_energy_expectation_1d(
    state: JanusQuantumState1D,
    sources: list[PointSource],
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> float:
    positive_h = janus_sector_hamiltonian_1d(
        state.grid,
        state.mass_abs,
        Sector.POSITIVE,
        sources,
        hbar=state.hbar,
        boundary_condition=boundary_condition,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )
    negative_h = janus_sector_hamiltonian_1d(
        state.grid,
        state.mass_abs,
        Sector.NEGATIVE,
        sources,
        hbar=state.hbar,
        boundary_condition=boundary_condition,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )
    energy = expectation_value_1d(state.grid, state.positive, positive_h)
    energy += expectation_value_1d(state.grid, state.negative, negative_h)
    if abs(energy.imag) > 1e-10:
        raise ValueError("energy expectation has a non-negligible imaginary part.")
    return float(energy.real)


def evolve_janus_state_1d(
    state: JanusQuantumState1D,
    sources: list[PointSource],
    dt: float,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.DIRICHLET,
    gravitational_constant: float = 1.0,
    softening: float = 0.0,
) -> JanusQuantumState1D:
    """Evolve both sectors without direct quantum-sector mixing."""

    positive_h = janus_sector_hamiltonian_1d(
        state.grid,
        state.mass_abs,
        Sector.POSITIVE,
        sources,
        hbar=state.hbar,
        boundary_condition=boundary_condition,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )
    negative_h = janus_sector_hamiltonian_1d(
        state.grid,
        state.mass_abs,
        Sector.NEGATIVE,
        sources,
        hbar=state.hbar,
        boundary_condition=boundary_condition,
        gravitational_constant=gravitational_constant,
        softening=softening,
    )
    return JanusQuantumState1D(
        state.grid,
        unitary_step_1d(state.positive, positive_h, dt, hbar=state.hbar),
        unitary_step_1d(state.negative, negative_h, dt, hbar=state.hbar),
        state.mass_abs,
        hbar=state.hbar,
    )


def schrodinger_poisson_step_1d(
    state: JanusQuantumState1D,
    dt: float,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.PERIODIC,
    gravitational_constant: float = 1.0,
) -> JanusQuantumState1D:
    """One explicit nonlinear step with potentials frozen from the input state."""

    positive_h, negative_h = janus_schrodinger_poisson_hamiltonians_1d(
        state,
        boundary_condition=boundary_condition,
        gravitational_constant=gravitational_constant,
    )
    return JanusQuantumState1D(
        state.grid,
        unitary_step_1d(state.positive, positive_h, dt, hbar=state.hbar),
        unitary_step_1d(state.negative, negative_h, dt, hbar=state.hbar),
        state.mass_abs,
        hbar=state.hbar,
    )


def run_schrodinger_poisson_1d(
    state: JanusQuantumState1D,
    steps: int,
    dt: float,
    boundary_condition: BoundaryCondition | str = BoundaryCondition.PERIODIC,
    gravitational_constant: float = 1.0,
) -> SchrodingerPoissonRun1D:
    if steps < 0:
        raise ValueError("steps must be non-negative.")

    energies: list[float] = []
    positive_probabilities: list[float] = []
    negative_probabilities: list[float] = []
    separations: list[float] = []
    current = state
    for step in range(steps + 1):
        energies.append(
            schrodinger_poisson_energy_1d(
                current,
                boundary_condition=boundary_condition,
                gravitational_constant=gravitational_constant,
            )
        )
        positive_probabilities.append(sector_probability_1d(current.grid, current.positive))
        negative_probabilities.append(sector_probability_1d(current.grid, current.negative))
        separations.append(sector_centroid_separation_1d(current))
        if step < steps:
            current = schrodinger_poisson_step_1d(
                current,
                dt=dt,
                boundary_condition=boundary_condition,
                gravitational_constant=gravitational_constant,
            )

    return SchrodingerPoissonRun1D(
        current,
        np.asarray(energies, dtype=float),
        np.asarray(positive_probabilities, dtype=float),
        np.asarray(negative_probabilities, dtype=float),
        np.asarray(separations, dtype=float),
    )
