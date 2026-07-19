from scripts.audit_program_m_configuration_composition import run_audit


def test_configuration_composition_audit_passes() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["finite_example"]["cross_composites_with_identical_one_point_pieces"] == 4


def test_interaction_is_not_claimed_by_relational_composition() -> None:
    assert "no geometry, dynamics or physical interaction" in run_audit()["scope"]
