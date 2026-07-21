from scripts.audit_program_m_geometry_bifurcation import run_audit


def test_free_preorder_does_not_select_unique_rank_geometry() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
    assert audit["candidate_reconstruction"]["realizers"] == 6
    assert audit["candidate_reconstruction"]["inequivalent_metric_classes"] == 2
    assert audit["missing_information"].startswith("a reconstruction or selection")
