from __future__ import annotations

from scripts.audit_janus_exact_solution_normalization import build_audit


def test_exact_solution_symbolic_normalization_audit() -> None:
    audit = build_audit()

    assert audit.all_symbolic_checks_pass
    assert audit.friedmann_identity_residual == "0"
    assert audit.corrected_ode_residual == "0"
    assert audit.source_bridge_map_residual == "0"
    assert "A" in audit.a2_d2a_dt2
    assert "c" in audit.a2_d2a_dt2
    assert "E" in audit.displayed_ode_residual
    assert audit.casimir_planck_coefficient_for_1e26m > 1.0e119
