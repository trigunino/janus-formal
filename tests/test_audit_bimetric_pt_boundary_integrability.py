from scripts.audit_bimetric_pt_boundary_integrability import (
    build_payload,
    corner_residual,
    null_rescaling_residual,
)


def test_paired_flux_gives_local_integrability_only():
    closure = build_payload()["closure"]
    assert closure["paired_flux_cancellation"]
    assert closure["local_integrability_criterion"]
    assert not closure["global_charge_integrability"]
    assert closure["corner_joint_functional_derived"]
    assert closure["conditional_corner_cancellation_proved"]
    assert closure["canonical_p_throat_causal_type_decided"]
    assert not closure["canonical_p_throat_requires_null_normal_fixing"]


def test_weighted_pt_corner_pair_cancels():
    assert corner_residual(2, 3, 5, 3, 2, -5) == 0
    assert corner_residual(2, 3, 5, 3, 2, -4) != 0


def test_null_rescaling_requires_equal_weighted_areas():
    assert null_rescaling_residual(6, 6, 2) == 0
    assert null_rescaling_residual(6, 5, 2) == 2
