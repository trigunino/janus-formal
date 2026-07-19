from scripts.audit_program_m_selection_from_axioms_nogo import run_audit


def test_no_axiom_profile_selector_can_distinguish_the_models() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert len(report["all_profile_based_selectors"]) == 2
    assert not any(
        row["matches_desired_selection"]
        for row in report["all_profile_based_selectors"]
    )
