from scripts.audit_program_m_signed_involution import run_audit


def test_signed_involution_requires_twisted_equivariance() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
    assert audit["odd_charge_candidates"] == [[1, -1], [2, -2], [3, -3]]
    assert audit["simultaneously_invariant_and_odd"] == [[0, 0]]
