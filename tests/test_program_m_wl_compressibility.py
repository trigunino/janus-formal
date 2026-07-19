import numpy as np

from scripts.audit_program_m_branch_adversary import repeated_two_level_branches
from scripts.audit_program_m_intrinsic_link_fluctuations import conditioned_poisson_order
from scripts.audit_program_m_wl_compressibility import (
    orientation_symmetric_wl,
    wl_compressibility_audit,
)


def test_wl_profile_is_relabelling_invariant() -> None:
    order = conditioned_poisson_order(48, 1234)
    permutation = np.random.default_rng(8).permutation(len(order))
    relabelled = order[np.ix_(permutation, permutation)]
    assert orientation_symmetric_wl(order)["class_size_profile"] == (
        orientation_symmetric_wl(relabelled)["class_size_profile"]
    )


def test_wl_profile_is_orientation_reversal_invariant() -> None:
    order = conditioned_poisson_order(48, 1234)
    assert orientation_symmetric_wl(order)["class_size_profile"] == (
        orientation_symmetric_wl(order.T)["class_size_profile"]
    )


def test_wl_detects_repeated_branches_beyond_exact_twins() -> None:
    report = orientation_symmetric_wl(repeated_two_level_branches(8, 1234))
    assert report["largest_stable_class"] >= 8


def test_calibrated_wl_gate_rejects_registered_repetition_controls() -> None:
    audit = wl_compressibility_audit()
    row = next(row for row in audit["rows"] if row["cardinality"] == 256)
    assert row["upper_threshold"] == 2
    assert all(not control["accepted"] for control in row["controls"])
