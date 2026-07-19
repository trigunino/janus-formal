from scripts.audit_program_m_exact_certificate_hypotheses import run_audit


def test_exact_certificate_keeps_all_gaps_visible() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
    assert not audit["safe_claims"]["exact_unconditional_minkowski_identification"]
    assert "exchangeable_random_realizer_lift" not in audit["blocking_exact_claim"]
