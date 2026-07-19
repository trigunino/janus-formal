from scripts.audit_program_m_candidate_kernel_axioms import CANDIDATES, run_audit


def test_candidate_list_does_not_encode_dimension_two() -> None:
    assert "dimension_two" not in CANDIDATES
    assert "transitively_orientable_incomparability" not in CANDIDATES


def test_natural_candidate_axioms_have_a_3d_countermodel() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    row_3d = next(row for row in report["rows"] if row["latent_dimension"] == 3)
    assert row_3d["dimension_two_violations"] > 0
