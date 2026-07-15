import numpy as np

from scripts.audit_bimetric_real_square_root_domain import (
    build_payload,
    evolution_budget_certificate,
    proportional_tube_certificate,
)


def test_pointwise_domain_and_global_limit_are_distinguished():
    payload = build_payload()
    closure = payload["closure"]
    assert closure["pointwise_spectral_domain_classified"]
    assert closure["positive_proportional_branch_in_domain"]
    assert not closure["global_spacetime_avoidance_proved"]
    assert "Jordan" in payload["general_real_root_criterion"]


def test_quantitative_tube_certifies_non_symmetric_perturbation():
    matrix = 4 * np.eye(4)
    matrix[0, 1] = 0.5
    certificate = proportional_tube_certificate(matrix, c=2)
    assert certificate["principal_root_certified"]
    assert certificate["right_half_plane_margin"] == 3.5
    assert min(np.linalg.eigvals(matrix).real) > 0


def test_tube_and_evolution_boundaries_are_strict():
    assert not proportional_tube_certificate(np.zeros((2, 2)), c=1)["principal_root_certified"]
    assert evolution_budget_certificate(2, 1, 2.9)["tube_preserved"]
    assert not evolution_budget_certificate(2, 1, 3)["tube_preserved"]
