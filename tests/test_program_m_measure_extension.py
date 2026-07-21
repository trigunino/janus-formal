from scripts.audit_program_m_measure_extension import run_audit


def test_measure_extension_exposes_uniformity_axiom() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
    assert audit["counts"] == {
        "positive_integer_measures": 27,
        "relationally_invariant": 27,
        "relationally_invariant_after_first_atom_normalization": 9,
        "fully_relabelling_invariant": 3,
        "fully_relabelling_invariant_after_normalization": 1,
    }
