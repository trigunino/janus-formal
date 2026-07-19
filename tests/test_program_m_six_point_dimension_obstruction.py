import numpy as np

from scripts.audit_program_m_six_point_dimension_obstruction import is_standard_s3, run_audit
from scripts.audit_program_m_two_order_representation import standard_example_s3


def test_s3_recognizer_is_relabeling_invariant() -> None:
    s3 = standard_example_s3()
    permutation = np.array([4, 1, 5, 0, 3, 2])
    assert is_standard_s3(s3)
    assert is_standard_s3(s3[np.ix_(permutation, permutation)])


def test_nearby_height_two_order_is_not_s3() -> None:
    s3 = standard_example_s3()
    s3[0, 3] = True
    assert not is_standard_s3(s3)


def test_six_point_obstruction_audit_passes() -> None:
    assert all(run_audit()["gates"].values())
