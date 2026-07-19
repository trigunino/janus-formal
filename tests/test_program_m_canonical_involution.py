from scripts.audit_program_m_canonical_involution import run_audit


def test_involution_existence_does_not_imply_canonical_choice() -> None:
    audit = run_audit()
    assert audit["protocol"] == {"rank": 3, "relations": 512}
    assert all(audit["gates"].values())
    witness = audit["empty_relation_witness"]
    assert len(witness["automorphisms"]) == 6
    assert len(witness["involutions"]) == 4
    assert witness["central_involutions"] == [[0, 1, 2]]
