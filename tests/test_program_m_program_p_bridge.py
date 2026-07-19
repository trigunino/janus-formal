from scripts.audit_program_m_program_p_bridge import run_audit


def test_program_p_bridge_is_non_geometric_and_complete() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["earliest_non_geometric_bridge"] == [
        "configuration carrier",
        "admissible maps or symmetries",
        "scalar codomain and candidate functionals",
    ]


def test_janus_specialization_is_not_smuggled_into_core() -> None:
    report = run_audit()
    janus = next(row for row in report["inputs"] if row["id"] == "PB-JANUS-01")
    assert janus["class"] == "janus_specialization"
