from scripts.audit_program_m_equivariant_gluing import run_audit


def test_equivariant_interface_is_exact_descent_gate() -> None:
    audit = run_audit()
    assert audit["protocol"] == {
        "piece_involution_pairs": 4,
        "partial_interfaces": 7,
        "cases": 28,
    }
    assert all(audit["gates"].values())
    assert audit["counts"]["equivariant_descents"] > 0
    assert audit["counts"]["rejected_interfaces"] > 0
