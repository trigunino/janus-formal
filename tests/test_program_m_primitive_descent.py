from scripts.audit_program_m_primitive_descent import run_audit


def test_primitive_descent_and_reachability_are_separated() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["example"]["globals_compatible_with_restrictions_only"] == 4
    assert report["example"]["globals_satisfying_primitive_descent"] == 1
