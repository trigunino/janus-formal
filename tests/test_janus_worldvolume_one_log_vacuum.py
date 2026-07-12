from __future__ import annotations

from scripts.audit_janus_worldvolume_one_log_vacuum import build_audit


def test_one_log_vacuum_symbolic_closure() -> None:
    audit = build_audit()

    assert audit.all_symbolic_checks_pass
    assert audit.derivative_factorization_residual == "0"
    assert audit.stable_for_positive_log_coefficient
    assert "exp" in audit.stationary_condensate
    assert "b" in audit.vacuum_energy
    assert "b" in audit.radial_curvature
