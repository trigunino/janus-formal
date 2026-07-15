import numpy as np

from janus_lab.sigma_thermodynamics import (
    entropy_production,
    linear_flux,
    onsager_casimir_residual,
    second_law_satisfied,
    total_energy_residual,
    moving_interface_residual,
    relax_linear,
    quadratic_lyapunov,
    von_neumann_entropy,
    partial_trace_two_qubit,
    two_qubit_mutual_information,
)


def test_closed_exchange_energy_balance():
    assert total_energy_residual(-3.0, 3.0) == 0.0
    assert total_energy_residual(2.0, 3.0, sigma_rate=-5.0) == 0.0


def test_equal_and_opposite_parity_onsager_casimir():
    reciprocal = np.array([[2.0, 0.3], [0.3, 1.0]])
    antisymmetric_cross = np.array([[2.0, 0.3], [-0.3, 1.0]])
    assert np.allclose(onsager_casimir_residual(reciprocal, np.array([1, 1])), 0.0)
    assert np.allclose(
        onsager_casimir_residual(antisymmetric_cross, np.array([1, -1])), 0.0
    )


def test_antisymmetric_part_is_entropy_neutral():
    symmetric = np.array([[2.0, 0.2], [0.2, 1.0]])
    antisymmetric = np.array([[0.0, 0.7], [-0.7, 0.0]])
    force = np.array([0.4, -1.2])
    np.testing.assert_allclose(
        entropy_production(symmetric + antisymmetric, force),
        entropy_production(symmetric, force),
    )


def test_second_law_accepts_psd_and_rejects_negative_direction():
    safe = np.array([[2.0, 0.5], [0.5, 1.0]])
    unsafe = np.array([[-1.0, 0.0], [0.0, 1.0]])
    assert second_law_satisfied(safe)
    assert not second_law_satisfied(unsafe)
    assert entropy_production(unsafe, np.array([1.0, 0.0])) < 0.0
    assert np.allclose(linear_flux(safe, np.ones(2)), np.array([2.5, 1.5]))


def test_moving_interface_jump_and_relaxation_lyapunov():
    source = 3.0 - 1.0 - 0.5 * (4.0 - 2.0)
    assert moving_interface_residual(3.0, 1.0, 0.5, 4.0, 2.0, source) == 0.0
    matrix = np.array([[2.0, 0.2], [0.2, 1.0]])
    history = relax_linear(matrix, np.array([1.0, -0.5]), np.linspace(0.0, 3.0, 20))
    lyapunov = np.array([quadratic_lyapunov(row) for row in history])
    assert np.all(np.diff(lyapunov) <= 1.0e-12)


def test_bell_state_has_entanglement_not_thermodynamic_production():
    bell = np.array([1.0, 0.0, 0.0, 1.0], dtype=complex) / np.sqrt(2.0)
    rho = np.outer(bell, bell.conj())
    reduced = partial_trace_two_qubit(rho, 1)
    np.testing.assert_allclose(von_neumann_entropy(rho), 0.0, atol=1.0e-12)
    np.testing.assert_allclose(von_neumann_entropy(reduced), np.log(2.0))
    np.testing.assert_allclose(
        two_qubit_mutual_information(rho), 2.0 * np.log(2.0)
    )
