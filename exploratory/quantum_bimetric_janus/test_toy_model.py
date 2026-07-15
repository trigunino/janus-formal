import numpy as np

from action_ansatz import induced_coupling_from_action
from compare_models import evaluate
from minisuperspace_model import induced_coupling
from toy_two_sector import evolve, hamiltonian


def test_identical_metrics_decouple():
    assert induced_coupling_from_action(1.0) == 0.0
    result = evaluate(omega_minus=1.0, coupling=0.0)
    assert result["concurrence"] == 0.0
    assert result["chsh_max"] == 2.0


def test_evolution_is_unitary_for_both_energy_signs():
    initial = np.array([1, 0, 0, 0], dtype=complex)
    for omega_minus in (1.0, -1.0):
        state = evolve(initial, hamiltonian(omega_minus=omega_minus, coupling=0.2), 1.0)
        assert np.isclose(np.vdot(state, state).real, 1.0)


def test_metric_mismatch_can_violate_chsh_in_toy_model():
    result = evaluate(omega_minus=1.0, coupling=induced_coupling_from_action(1.5))
    assert result["chsh_max"] > 2.0


def test_minisuperspace_exchange_symmetry():
    for ratio in (0.6, 0.8, 1.2, 1.7):
        plus = evaluate(omega_minus=1.0, coupling=induced_coupling(ratio))
        exchanged = evaluate(omega_minus=1.0, coupling=induced_coupling(1.0 / ratio))
        assert np.isclose(plus["concurrence"], exchanged["concurrence"])
        assert np.isclose(plus["chsh_max"], exchanged["chsh_max"])
