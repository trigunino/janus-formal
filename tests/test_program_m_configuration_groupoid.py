from scripts.audit_program_m_configuration_groupoid import run_audit


def test_configuration_groupoid_audit_passes() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["finite_example"]["automorphism_count"] == 3


def test_configuration_groupoid_scope_is_pregeometric() -> None:
    scope = run_audit()["scope"]
    assert "no topology" in scope
    assert "physical action" in scope
