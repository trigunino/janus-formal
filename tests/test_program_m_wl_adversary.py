import numpy as np

from scripts.audit_program_m_wl_adversary import (
    graduated_chain_fan,
    wl_adversary_audit,
)
from scripts.audit_program_m_wl_compressibility import orientation_symmetric_wl


def test_graduated_fan_is_partial_order_and_wl_individualized() -> None:
    order = graduated_chain_fan(6, 1234)
    assert np.all(np.diag(order))
    assert np.all(~(order & order.T) | np.eye(len(order), dtype=bool))
    assert np.all((order.astype(int) @ order.astype(int) > 0) <= order)
    assert orientation_symmetric_wl(order)["largest_stable_class"] <= 2


def test_asymmetric_compressible_fan_breaks_all_five_gates() -> None:
    audit = wl_adversary_audit()
    assert audit["total_all_five_collisions"] > 0
    assert audit["largest_passing_maximum_chain_length"] >= 5
    assert audit["status"] == "one_wl_repair_broken_by_asymmetric_compressible_fan"
