from scripts.audit_program_m_rank_four_forcing import (
    FORCING_SET,
    rank_four_poset_classes,
    run_audit,
)


def test_rank_four_classes_partition_all_permutations() -> None:
    classes = rank_four_poset_classes()
    patterns = [pattern for members in classes.values() for pattern in members]
    assert len(classes) == 16
    assert len(patterns) == len(set(patterns)) == 24


def test_forcing_set_is_exact_union_of_whole_poset_classes() -> None:
    selected = [
        set(patterns)
        for patterns in rank_four_poset_classes().values()
        if set(patterns) <= FORCING_SET
    ]
    assert set().union(*selected) == FORCING_SET


def test_rank_four_forcing_certificate_passes() -> None:
    assert all(run_audit()["gates"].values())
