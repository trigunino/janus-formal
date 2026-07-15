from __future__ import annotations

from scripts.derive_janus_worldvolume_gauge_sextic_vertices import build_audit


def test_order_six_contains_required_direct_vertex() -> None:
    audit = build_audit(6)
    assert audit.coefficient_formula_verified
    assert audit.coefficients["eta6_F2"] == "7/v**8"
    assert audit.direct_eta6_vertex_present
    assert audit.sufficient_for_one_loop_six_point_bookkeeping


def test_quadratic_truncation_is_not_complete_for_six_point_loop() -> None:
    audit = build_audit(2)
    assert not audit.direct_eta6_vertex_present
    assert audit.verdict == "increase_expansion_to_order_six"


def test_linear_quadratic_ring_partitions_are_complete() -> None:
    assert build_audit().linear_quadratic_ring_partitions == (
        (6, 0),
        (4, 1),
        (2, 2),
        (0, 3),
    )
