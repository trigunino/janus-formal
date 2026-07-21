from scripts.audit_program_m_weight_selection_nogo import run_audit


def test_relations_do_not_select_relative_primitive_weights() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
    assert audit["counts"] == {
        "invariant_and_gluable": 9,
        "after_fixing_first_edge_to_one": 3,
        "distinct_normalized_ratios": 3,
    }
    assert audit["witness"]["automorphisms"] == [[0, 1, 2]]
