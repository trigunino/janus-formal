from scripts.derive_bimetric_lambda3_cubic_eom import build_payload


def test_cubic_eom_is_single_galileon_invariant():
    payload = build_payload()
    assert payload["factorization_exact"]
    assert payload["coefficient"] == "(2*betaHat1 - 3*betaHat2)/2"
    assert payload["spherical_U2"] == "2*lambda_t*(2*lambda_r + lambda_t)"


def test_normalization_boundary_is_explicit():
    closure = build_payload()["closure"]
    assert closure["dual_frame_coefficient"]
    assert not closure["candidate_beta_normalization_map"]
    assert not closure["full_bigravity_two_frame_coefficient"]
