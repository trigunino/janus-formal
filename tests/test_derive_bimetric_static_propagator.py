from scripts.derive_bimetric_static_propagator import build_payload


def test_exact_inverse_and_pole_decomposition():
    payload = build_payload()
    assert payload["inverse_matches_pole_decomposition"]
    assert payload["inverse_identity"]
    assert payload["massive_pole_mass2"] == "mu*(K_minus + K_plus)/(K_minus*K_plus)"


def test_yukawa_signs_and_limits_are_explicit():
    payload = build_payload()
    assert payload["cross_yukawa_ratio"] == "-1"
    assert "diag" in payload["limits"]["short_distance"]
    assert "Vainshtein" in payload["scope"]
