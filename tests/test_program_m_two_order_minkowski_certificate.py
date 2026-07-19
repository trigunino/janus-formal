from scripts.audit_program_m_two_order_minkowski_certificate import run_audit


def test_combined_two_order_minkowski_certificate_passes() -> None:
    assert all(run_audit()["gates"].values())
