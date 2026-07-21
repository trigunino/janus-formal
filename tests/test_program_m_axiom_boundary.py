from scripts.audit_program_m_axiom_boundary import run_audit


def test_axiom_boundary_has_no_unearned_candidate() -> None:
    report = run_audit()
    assert all(report["gates"].values())
    assert report["counts"] == {
        "too_weak": 4,
        "circular": 3,
        "open_not_yet_admissible": 0,
    }


def test_separator_shortcut_is_marked_circular() -> None:
    report = run_audit()
    row = next(
        row for row in report["rows"]
        if row["axiom"] == "two_reversible_families_of_critical_pairs"
    )
    assert row["class"] == "circular"
