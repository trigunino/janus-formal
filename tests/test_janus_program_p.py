from __future__ import annotations

from scripts.audit_janus_program_p import assert_program_p_gate_integrity


def test_program_p_gates_are_integrated() -> None:
    assert_program_p_gate_integrity()


def test_program_p_effective_d8_field_base_bridge_is_integrated() -> None:
    assert_program_p_gate_integrity()


def test_program_p_weighted_l2_lattice_exactness_is_integrated() -> None:
    assert_program_p_gate_integrity()


def test_program_p_minkowski_diagonal_local_relative_root_is_integrated() -> None:
    assert_program_p_gate_integrity()


def test_program_p_minkowski_relative_root_open_domain_is_integrated() -> None:
    assert_program_p_gate_integrity()


def test_program_p_minkowski_candidate_a_variation_is_integrated() -> None:
    assert_program_p_gate_integrity()


def test_program_p_effective_d8_continuous_field_spaces_are_integrated() -> None:
    assert_program_p_gate_integrity()


def test_program_p_d10_finite_mode_determinant_line_is_integrated() -> None:
    assert_program_p_gate_integrity()


def test_program_p_d10_infinite_circle_common_domain_is_integrated() -> None:
    assert_program_p_gate_integrity()
