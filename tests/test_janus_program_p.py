from __future__ import annotations

from scripts.audit_janus_program_p import assert_program_p_gate_integrity


def test_program_p_gates_are_integrated() -> None:
    assert_program_p_gate_integrity()
