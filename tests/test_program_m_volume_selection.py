from fractions import Fraction

from scripts.audit_program_m_embedding_ambiguity import product_order_realizers
from scripts.audit_program_m_volume_selection import (
    canonical_partial_orders,
    interval_count_volume_fit,
    volume_selection_audit,
)


def test_forward_generation_recovers_known_unlabeled_poset_counts() -> None:
    assert [len(canonical_partial_orders(size)) for size in range(1, 6)] == [
        1,
        2,
        5,
        16,
        63,
    ]


def test_density_fit_is_exact_for_two_element_chain() -> None:
    size = 2
    mask = (1 << 0) | (1 << 1) | (1 << 3)
    coordinates = product_order_realizers(mask, size)[0]
    fit = interval_count_volume_fit(mask, size, coordinates)
    assert Fraction(*fit["calibrated_density"]) == 4
    assert fit["validation_sum_squared_count_residual"] is None


def test_volume_fit_has_limited_selection_power() -> None:
    rows = volume_selection_audit(5)["rows"]
    assert rows[3]["metric_ambiguous_classes"] == 1
    assert rows[3]["uniquely_selected_by_volume_fit"] == 0
    assert rows[4]["metric_ambiguous_classes"] == 10
    assert rows[4]["uniquely_selected_by_volume_fit"] == 2
    assert rows[4]["unresolved_after_volume_fit"] == 8
