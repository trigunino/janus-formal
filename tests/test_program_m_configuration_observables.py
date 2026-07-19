from scripts.audit_program_m_configuration_observables import run_audit


def test_configuration_observable_audit_accepts_structure_not_labels() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["observables"]["edge_count"]
    assert not report["observables"]["label_zero_out_degree"]
