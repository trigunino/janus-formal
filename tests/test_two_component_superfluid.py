import numpy as np
import pytest

from janus_lab.two_component_superfluid import (
    acoustic_step_scattering,
    bogoliubov_frequency_squared,
    healing_lengths,
    imaginary_time_ground_state,
    interaction_eigenvalues,
    miscible_stable,
    mode_conversion_probability,
    sound_speeds_squared,
)


def test_miscibility_and_interaction_spectrum():
    assert miscible_stable(1.0, 1.0, 0.4)
    assert not miscible_stable(1.0, 1.0, 1.2)
    assert np.all(interaction_eigenvalues(1.0, 1.0, 0.4) > 0.0)


def test_bogoliubov_branches_are_stable_on_cone():
    k = np.linspace(0.0, 3.0, 100)
    common, relative = bogoliubov_frequency_squared(k, 1.0, 1.0, 1.0, 0.4)
    assert np.all(common >= 0.0)
    assert np.all(relative >= 0.0)
    common_c2, relative_c2 = sound_speeds_squared(1.0, 1.0, 1.0, 0.4)
    assert common_c2 > relative_c2 > 0.0
    assert all(value > 0.0 for value in healing_lengths(1.0, 1.0, 1.0, 0.4))


def test_relative_branch_detects_immiscible_instability():
    _, relative = bogoliubov_frequency_squared(0.1, 1.0, 1.0, 1.0, 1.2)
    assert relative < 0.0
    with pytest.raises(ValueError):
        imaginary_time_ground_state(g=1.0, g12=1.2)


def test_ground_state_relaxes_to_symmetric_miscible_background():
    result = imaginary_time_ground_state(points=64, steps=150, seed=4)
    assert np.std(result["psi1"]) < 1.0e-2
    assert np.std(result["psi2"]) < 1.0e-2
    assert np.allclose(np.sum(result["psi1"] ** 2), 64.0)


def test_sf04_scattering_conserves_flux_and_conversion_is_bounded():
    scattering = acoustic_step_scattering(1.0, 2.0)
    assert scattering["reflection_flux"] + scattering["transmission_flux"] == pytest.approx(1.0)
    assert acoustic_step_scattering(1.0, 1.0)["reflection_flux"] == 0.0
    probability = mode_conversion_probability(0.3, 1.1)
    assert 0.0 <= probability <= 1.0
