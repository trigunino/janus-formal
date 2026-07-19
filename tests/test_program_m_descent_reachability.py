from scripts.audit_program_m_descent_reachability import run_audit


def test_descent_reachability_audit_passes() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["random_disagreements"] == 0
