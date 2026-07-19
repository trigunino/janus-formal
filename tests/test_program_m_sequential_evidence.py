from scripts.audit_program_m_sequential_evidence import (
    clopper_pearson_interval,
    run_audit,
    stage_alpha,
)


def test_alpha_spending_is_bounded() -> None:
    spent = 4 * sum(stage_alpha(0.025, stage) / 4 for stage in range(1, 10000))
    assert spent < 0.025


def test_zero_violations_still_has_positive_upper_bound() -> None:
    lower, upper = clopper_pearson_interval(0, 4096, 0.001)
    assert lower == 0.0 < upper


def test_sequential_evidence_audit_passes() -> None:
    assert all(run_audit()["gates"].values())
