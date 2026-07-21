from scripts.audit_program_m_archive_integrity import run_audit


def test_program_m_archive_is_complete_and_unambiguous() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["duplicate_provenance_ids"] == []
