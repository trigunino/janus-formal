from fractions import Fraction

from scripts.audit_program_m_chain_time_selection import (
    chain_time_fit,
    chain_time_selection_audit,
    intrinsic_chain_steps,
)
from scripts.audit_program_m_embedding_ambiguity import product_order_realizers


def test_intrinsic_chain_steps_uses_longest_chain() -> None:
    size = 3
    mask = sum(
        1 << (source * size + target)
        for source in range(size)
        for target in range(size)
        if source <= target
    )
    assert intrinsic_chain_steps(mask, size, 0, 2) == 2


def test_three_chain_calibrates_exact_squared_scale() -> None:
    size = 3
    mask = sum(
        1 << (source * size + target)
        for source in range(size)
        for target in range(size)
        if source <= target
    )
    fit = chain_time_fit(mask, size, product_order_realizers(mask, size)[0])
    assert Fraction(*fit["calibrated_chain_to_time_squared"]) == 1
    assert Fraction(*fit["validation_sum_squared_time2_residual"]) == 0


def test_volume_and_chain_time_conflict_without_joint_winner() -> None:
    row = chain_time_selection_audit(5)["rows"][-1]
    assert row["metric_ambiguous_classes"] == 10
    assert row["uniquely_selected_by_chain_time"] == 2
    assert row["volume_chain_time_conflicts"] == 2
    assert row["uniquely_pareto_dominant_jointly"] == 0
