from scripts.audit_program_m_exchangeable_realizer_lift import run_audit


def test_exchangeable_realizer_orbit_lift_passes() -> None:
    assert all(run_audit()["gates"].values())
