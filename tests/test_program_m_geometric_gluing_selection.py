from scripts.audit_program_m_geometric_gluing_selection import run_audit


def test_local_uniqueness_does_not_force_global_metric_uniqueness() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
    assert audit["metric_class_counts"] == {
        "patches": [1, 1],
        "interface": 1,
        "global": 2,
    }
    assert audit["diagram"]["unseen_pair"] == [2, 3]
