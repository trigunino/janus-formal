from scripts.derive_bimetric_helicity0_scalar_sector import build_payload


def test_only_one_healthy_physical_scalar_remains():
    payload = build_payload()
    assert payload["field_content"] == {
        "massless_scalar_modes": 0,
        "massive_helicity0_modes": 1,
        "bd_scalar_modes": 0,
    }
    assert payload["checks"]["helicity0_no_ghost_for_positive_kinetics"]
    assert payload["checks"]["no_gradient_instability"]
    assert payload["checks"]["no_tachyon_if_mu_positive"]


def test_massive_residue_has_one_positive_relative_sheet_direction():
    checks = build_payload()["checks"]
    assert checks["residue_rank"] == 1
    assert checks["residue_determinant_zero"]
    assert checks["residue_positive_semidefinite_for_positive_kinetics"]


def test_cosmological_scalar_claim_is_not_overstated():
    closure = build_payload()["closure"]
    assert closure["flat_quadratic_scalar_count"]
    assert not closure["cosmological_time_dependent_scalar_sector"]
    assert not closure["strong_coupling_scale_computed"]
