from scripts.audit_program_m_high_rank_dimension import PROTOCOL, run_audit


def test_high_rank_family_allocation_is_bounded() -> None:
    assert len(PROTOCOL["models"]) * len(PROTOCOL["ranks"]) * PROTOCOL["cell_alpha"] <= 0.05


def test_high_rank_dimension_audit_passes() -> None:
    assert all(run_audit()["gates"].values())
