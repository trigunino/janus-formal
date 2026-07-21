from scripts.audit_program_m_signed_program_p_adapter import run_audit


def test_signed_program_p_adapter_boundary_is_explicit() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
    assert all(audit["theorems"].values())
    assert len(audit["supplied_to_program_p"]) == 6
    assert len(audit["remains_external"]) == 8
