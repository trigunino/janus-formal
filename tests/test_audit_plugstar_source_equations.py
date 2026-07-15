from scripts.audit_plugstar_source_equations import build_payload


def test_quoted_critical_redshift_is_exactly_three():
    payload = build_payload()
    checks = payload["exact_checks"]
    assert checks["critical_compactness"] == "8/9"
    assert checks["quoted_redshift_lapse"] == "1/3"
    assert checks["quoted_wavelength_ratio"] == "3"


def test_source_does_not_close_static_plugstar_model():
    payload = build_payload()
    assert not payload["co02_ready"]
    assert "radial_stability" in payload["conjectured_or_missing"]
    assert "two-sector" in payload["next_required_atom"]
