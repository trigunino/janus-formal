from scripts.derive_bimetric_canonical_vainshtein_coefficient import build_payload


def test_pt_combined_coefficients_and_dual_cancellation():
    payload = build_payload()
    pt = payload["pt_branch"]
    assert pt["C2"] == "(b1 + b2)**2*(q2 + 1)/2"
    assert pt["C3"] == "(b1 + b2)**2"
    assert pt["minus_frame_cubic_after_duality"] == "0"
    assert all(value is True for value in list(payload["closure"].values())[:4])


def test_canonical_normalization_is_recorded():
    pt = build_payload()["pt_branch"]
    assert pt["canonical_field"] == "phi=sqrt(12*C2)*pi"
    assert "q2 + 1" in pt["canonical_cubic_g3"]
