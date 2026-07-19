import numpy as np

from scripts.audit_program_m_interval_multiscale import (
    PROTOCOL,
    is_transitive,
    run_audit,
    three_layer_order,
)


def test_three_layer_control_is_a_partial_order() -> None:
    order = three_layer_order(128, 17)
    assert np.all(np.diag(order))
    assert np.array_equal(order & order.T, np.eye(128, dtype=bool))
    assert is_transitive(order)


def test_multiscale_protocol_seed_ranges_are_disjoint() -> None:
    train_count = int(PROTOCOL["training_replicates_per_size"])
    validation_count = int(PROTOCOL["validation_replicates_per_size"])
    for index, _ in enumerate(PROTOCOL["sizes"]):
        base = int(PROTOCOL["base_seed"]) + 10_000 * index
        training = set(range(base, base + train_count))
        validation_base = base + int(PROTOCOL["validation_seed_offset"])
        validation = set(range(validation_base, validation_base + validation_count))
        assert training.isdisjoint(validation)


def test_multiscale_interval_gates() -> None:
    audit = run_audit()
    assert audit["protocol"] == PROTOCOL
    assert audit["gates"]["poisson_validation_all_scales"] is False
    assert audit["gates"]["grids_rejected_all_scales"] is True
    assert audit["gates"]["three_layer_rejected_all_scales"] is True
    assert audit["gates"]["three_layer_orders_all_transitive"] is True
    assert audit["gates"]["all_preregistered_gates"] is False
    failed_scale = next(row for row in audit["results"] if not row["validation_gate"])
    assert failed_scale["elements"] == 256
    assert failed_scale["validation_acceptance"] == 0.875
