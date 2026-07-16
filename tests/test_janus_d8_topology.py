from __future__ import annotations

from scripts.audit_janus_d8_topology import assert_d8_topology_integrity


def test_d8_topology_gate_is_integrated_without_smooth_overclaim() -> None:
    assert_d8_topology_integrity()


def test_d8_associated_normal_line_is_integrated_without_bundle_overclaim() -> None:
    assert_d8_topology_integrity()


def test_d8_mapping_torus_pt_involution_is_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_orientation_double_cover_is_topological_and_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_throat_complement_sides_are_integrated_without_component_overclaim() -> None:
    assert_d8_topology_integrity()


def test_d8_throat_complement_is_path_connected() -> None:
    assert_d8_topology_integrity()
