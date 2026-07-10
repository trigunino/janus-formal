from __future__ import annotations

from scripts.audit_janus_discrete_level_alpha import build_audit


def test_discrete_level_candidates_are_finite_and_positive() -> None:
    audit = build_audit()

    assert 130.0 < audit.target_hierarchy_exponent < 150.0
    assert len(audit.candidates) == 4
    for candidate in audit.candidates:
        assert candidate.nearest_level >= 1
        assert candidate.predicted_alpha_m > 0.0
        assert candidate.required_lambda_over_beta > 0.0


def test_larger_lock_constant_requires_larger_level_at_fixed_target() -> None:
    audit = build_audit(lock_constants=(1.0, 2.0, 4.0, 8.0))
    levels = [candidate.target_continuous_level for candidate in audit.candidates]

    assert levels == sorted(levels)
    assert levels[-1] > 10.0
