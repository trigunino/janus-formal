import numpy as np

from janus_lab.pt_phase_transition import (
    classify_stationary_points,
    equilibrium_order_parameter,
    potential,
    scale_selection_audit,
    stationary_points,
)


def test_potential_is_pt_even():
    phi = np.linspace(-3.0, 3.0, 101)
    assert np.allclose(potential(-phi, -1.0, 2.0), potential(phi, -1.0, 2.0))


def test_symmetric_and_broken_phases():
    assert np.array_equal(stationary_points(1.0, 1.0), np.array([0.0]))
    classified = classify_stationary_points(-2.0, 1.0)
    assert [row["kind"] for row in classified] == ["minimum", "maximum", "minimum"]
    assert classified[0]["phi"] == -1.0
    assert classified[2]["phi"] == 1.0


def test_thermal_transition_is_continuous_in_minimal_model():
    temperatures = np.array([0.0, 0.5, 1.0, 1.5])
    order = equilibrium_order_parameter(temperatures, 1.0, 1.0, 1.0)
    assert order[0] > order[1] > order[2]
    assert order[2] == 0.0
    assert order[3] == 0.0


def test_pt_alone_does_not_select_scale():
    blocked = scale_selection_audit(None, None)
    supplied = scale_selection_audit(-2.0, 1.0)
    assert not blocked["nonzero_scale_selected"]
    assert blocked["broken_scale"] is None
    assert supplied["broken_scale"] == 1.0
    assert "coefficient_ratio" in supplied["verdict"]
