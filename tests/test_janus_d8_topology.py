from __future__ import annotations

from functools import lru_cache

from scripts.audit_janus_d8_topology import assert_d8_topology_integrity


assert_d8_topology_integrity = lru_cache(maxsize=1)(
    assert_d8_topology_integrity
)


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


def test_d8_cover_atlases_and_topological_quotient_manifolds_are_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_smooth_deck_descent_data_is_integrated_without_quotient_overclaim() -> None:
    assert_d8_topology_integrity()


def test_d8_smooth_quotient_manifold_and_projection_are_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_pt_is_an_analytic_diffeomorphism() -> None:
    assert_d8_topology_integrity()


def test_d8_throat_is_a_global_smooth_embedding() -> None:
    assert_d8_topology_integrity()


def test_d8_throat_has_an_analytic_normal_vector_bundle() -> None:
    assert_d8_topology_integrity()


def test_d8_normal_family_and_global_z4_root_bundles_are_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_differential_normal_smooth_equivalence_is_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_differential_normal_zero_nonzero_strata_are_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_ambient_tangent_orientation_cocycle_is_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_ambient_tangent_quadratic_reduction_is_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_ambient_spin_projection_is_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_ambient_spin_projection_preserves_orientation() -> None:
    assert_d8_topology_integrity()


def test_d8_ambient_spin_atlas_obstruction_is_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_ambient_spin_overlap_torsor_is_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_global_z4_root_bundles_are_exchanged_by_pt_conjugation() -> None:
    assert_d8_topology_integrity()


def test_d8_normal_pin_minus_principal_bundle_is_integrated() -> None:
    assert_d8_topology_integrity()


def test_d8_effective_quotients_are_compact() -> None:
    assert_d8_topology_integrity()
