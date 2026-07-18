from scripts.audit_bimetric_nonnull_ghy_pt import (
    build_payload,
    paired_ghy_factor,
    overlap_ghy_density,
    equatorial_warp_data,
    pt_fixed_extrinsic_entry,
)


def test_double_sign_reversal_is_pt_even():
    assert paired_ghy_factor(1, -1, -1) == 2


def test_single_sign_reversal_cancels_at_equal_scales():
    assert paired_ghy_factor(1, -1, 1) == 0
    assert paired_ghy_factor(1, 1, -1) == 0


def test_invalid_parity_is_rejected():
    try:
        paired_ghy_factor(1, 0, 1)
    except ValueError:
        return
    raise AssertionError("invalid parity accepted")


def test_closure_does_not_claim_global_instantiation():
    closure = build_payload()["closure"]
    assert closure["sectorwise_eh_ghy_cancellation_available"]
    assert closure["local_gaussian_extrinsic_sign_law_proved"]
    assert not closure["canonical_atlas_gaussian_compatibility_proved"]
    assert not closure["cross_sheet_ghy_cancellation_generic"]
    assert not closure["canonical_throat_extrinsic_curvature_instantiated"]


def test_pt_fixed_and_odd_entry_is_zero_only():
    assert pt_fixed_extrinsic_entry(0, 0)["forced_zero"]
    assert not pt_fixed_extrinsic_entry(2, -2)["forced_zero"]


def test_sign_clutched_ghy_density_descends():
    certificate = overlap_ghy_density(-1, 2, 3)
    assert certificate["descends"]
    assert certificate["transformed"] == 6


def test_equatorial_warp_has_zero_extrinsic_curvature():
    data = equatorial_warp_data(0)
    assert data == {"warp": 1.0, "normal_derivative": 0.0,
                    "extrinsic_prefactor": 0.0}
