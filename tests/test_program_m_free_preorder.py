from scripts.audit_program_m_free_preorder import run_audit


def test_free_preorder_audit_is_exhaustive_and_passes() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["protocol"]["primitive_relations"] == 512
    assert report["failures"] == 0
