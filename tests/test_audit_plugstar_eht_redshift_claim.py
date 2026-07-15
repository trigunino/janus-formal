from scripts.audit_plugstar_eht_redshift_claim import build_payload


def test_image_intensity_ratio_is_not_spectral_redshift():
    payload = build_payload()
    assert not payload["logical_gates"]["single_frequency_intensity_is_wavelength_measurement"]
    assert payload["verdict"] == "ratio_3_is_not_an_EHT_spectral_redshift_measurement"


def test_forward_model_requirements_are_explicit():
    payload = build_payload()
    assert "covariant_radiative_transfer" in payload["required_forward_chain"]
    assert "synthetic_complex_visibilities" in payload["required_forward_chain"]
