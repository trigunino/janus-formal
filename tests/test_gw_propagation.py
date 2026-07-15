import numpy as np

from janus_lab.gw_propagation import (
    conversion_probability,
    flat_delay,
    flrw_massive_phase,
    group_velocity,
    mixing_matrix,
    propagate_modes,
)


def test_group_velocity_and_delay_limits():
    assert group_velocity(3.0, 0.0) == 1.0
    assert 0.0 < group_velocity(3.0, 2.0) < 1.0
    assert flat_delay(10.0, 3.0, 2.0) > 0.0


def test_mixing_is_orthogonal_and_probability_bounded():
    rotation = mixing_matrix(0.37)
    assert np.allclose(rotation.T @ rotation, np.eye(2))
    assert conversion_probability(0.0, 1.2) == 0.0
    assert 0.0 <= conversion_probability(0.37, 1.2) <= 1.0


def test_degenerate_phases_recover_state_up_to_common_phase():
    state = np.array([1.0 + 0.2j, -0.3j])
    result = propagate_modes(state, 0.41, np.array([0.7, 0.7]))
    assert np.allclose(result, np.exp(-0.7j) * state)


def test_flrw_phase_is_zero_for_massless_and_positive_for_massive():
    z = np.linspace(0.0, 1.0, 101)
    h = np.ones_like(z)
    assert flrw_massive_phase(z, h, 10.0, 0.0) == 0.0
    assert flrw_massive_phase(z, h, 10.0, 0.5) > 0.0
