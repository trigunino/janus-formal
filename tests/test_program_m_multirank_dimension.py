from scripts.audit_program_m_multirank_dimension import allocated_alpha, run_audit


def test_multirank_alpha_spending_is_bounded() -> None:
    spent = 4 * 3 * sum(allocated_alpha(stage) for stage in range(1, 10000))
    assert spent < 0.05


def test_multirank_dimension_audit_passes() -> None:
    assert all(run_audit()["gates"].values())
