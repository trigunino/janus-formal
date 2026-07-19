from scripts.audit_program_m_involution_composition import run_audit


def test_unique_intrinsic_involution_is_not_composition_stable() -> None:
    audit = run_audit()
    assert audit["protocol"]["ordered_compositions"] > 0
    assert all(audit["gates"].values())
    assert audit["counts"]["compositions_losing_uniqueness"] > 0
    assert (
        audit["counts"]["componentwise_involution_valid"]
        == audit["protocol"]["ordered_compositions"]
    )
