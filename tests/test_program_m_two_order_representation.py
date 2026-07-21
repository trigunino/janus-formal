import numpy as np

from scripts.audit_program_m_two_order_representation import (
    is_partial_order,
    run_audit,
    standard_example_s3,
    two_order_realizer,
)


def test_chain_and_antichain_have_two_order_realizers() -> None:
    chain = np.triu(np.ones((4, 4), dtype=bool))
    antichain = np.eye(4, dtype=bool)
    assert two_order_realizer(chain) is not None
    assert two_order_realizer(antichain) is not None


def test_standard_s3_is_partial_but_not_two_dimensional() -> None:
    s3 = standard_example_s3()
    assert is_partial_order(s3)
    assert two_order_realizer(s3) is None


def test_two_order_representation_audit_passes() -> None:
    assert all(run_audit()["gates"].values())
