import numpy as np

from scripts.audit_program_m_poisson_minkowski2 import (
    PROTOCOL,
    longest_product_chain,
    one_replicate,
    run_audit,
)


def test_longest_product_chain_known_examples() -> None:
    chain = np.array([[0.0, 0.0], [0.5, 0.5], [1.0, 1.0]])
    antichain = np.array([[0.0, 1.0], [0.5, 0.5], [1.0, 0.0]])
    assert longest_product_chain(chain) == 3
    assert longest_product_chain(antichain) == 1


def test_replicate_is_seed_reproducible() -> None:
    first = one_replicate(256, int(PROTOCOL["base_seed"]))
    second = one_replicate(256, int(PROTOCOL["base_seed"]))
    assert first == second


def test_preregistered_regions_have_equal_target_volume_and_time() -> None:
    products = [u * v for u, v in (r["upper"] for r in PROTOCOL["equal_volume_regions"])]
    assert all(abs(product - 0.25) < 1e-15 for product in products)


def test_preregistered_audit_passes_without_threshold_mutation() -> None:
    audit = run_audit()
    assert audit["protocol"]["thresholds"] == PROTOCOL["thresholds"]
    assert audit["gates"]["all_preregistered_gates"] is True
