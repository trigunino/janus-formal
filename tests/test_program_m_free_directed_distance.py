import math

from scripts.audit_program_m_free_directed_distance import (
    run_audit,
    shortest_distances,
)


def test_two_step_chain_has_expected_directed_distance() -> None:
    size = 3
    mask = (1 << 1) | (1 << (size + 2))
    distance = shortest_distances(mask, size)
    assert distance[0][2] == 2
    assert math.isinf(distance[2][0])


def test_exhaustive_directed_distance_audit() -> None:
    audit = run_audit()
    assert audit["protocol"]["relations"] == 65_536
    assert audit["failures"] == 0
    assert all(audit["gates"].values())
