from __future__ import annotations

from scripts.audit_janus_worldvolume_one_loop_anomalous_dimension import build_audit


def test_integer_power_one_loop_integrals_have_no_three_dimensional_ms_pole() -> None:
    audit = build_audit()
    assert audit.one_loop_ms_wavefunction_pole == "0"
    assert set(audit.pole_residues) == {"0"}
    assert audit.verdict == "no_one_loop_ms_anomalous_dimension_for_integer_power_bubbles"


def test_gamma_arguments_are_half_integer() -> None:
    audit = build_audit(4)
    assert audit.gamma_arguments_at_epsilon_zero == ("-1/2", "1/2", "3/2", "5/2")
