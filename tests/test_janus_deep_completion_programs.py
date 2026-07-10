from __future__ import annotations

from scripts.audit_janus_nonlinear_bimetric_completion import (
    build_audit as build_bimetric_audit,
)
from scripts.audit_janus_worldvolume_quantum_completion import (
    build_audit as build_quantum_audit,
)


def test_quantum_worldvolume_hierarchy_is_moderate_but_sensitive() -> None:
    audit = build_quantum_audit()

    assert audit.hierarchy_ratio > 1.0e60
    assert 130.0 < audit.hierarchy_exponent < 150.0
    assert 0.4 < audit.required_beta0_g_squared < 0.8
    assert 0.15 < audit.coupling_for_beta0_11 < 0.35
    assert audit.log_sensitivity_to_coupling < -250.0
    assert audit.required_ll_charge_inverse_m2 > 0.0
    assert not audit.flat_direction_predictive


def test_nonlinear_bimetric_relational_closure() -> None:
    audit = build_bimetric_audit()

    assert audit.all_symbolic_checks_pass
    assert audit.reciprocity_condition == "plusFromMinus = minusFromPlus"
    assert audit.selected_positive_radial_coordinate == "r = 1"
    assert audit.proportional_potential_swap_residual == "0"
    assert audit.pt_symmetric_free_potential_coefficients == 3
    assert not audit.absolute_scale_fixed_by_dimensionless_action_data
