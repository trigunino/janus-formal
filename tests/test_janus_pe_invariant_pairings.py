from __future__ import annotations

from scripts.audit_janus_pe_invariant_pairings import build_audit


def _dimension_map() -> dict[tuple[str, str], tuple[int, int]]:
    audit = build_audit()
    return {
        (entry.left, entry.right): (
            entry.cubic_dimension,
            entry.continuous_o3_dimension,
        )
        for entry in audit.pairing_dimensions
    }


def test_low_rank_invariant_pairing_dimensions() -> None:
    audit = build_audit()
    dimensions = _dimension_map()

    assert audit.all_checks_pass
    assert dimensions[("scalar", "scalar")] == (1, 1)
    assert dimensions[("scalar", "vector")] == (0, 0)
    assert dimensions[("scalar", "traceless")] == (0, 0)
    assert dimensions[("vector", "vector")] == (1, 1)
    assert dimensions[("vector", "traceless")] == (0, 0)


def test_continuous_rotations_remove_cubic_tensor_freedom() -> None:
    audit = build_audit()
    dimensions = _dimension_map()

    assert dimensions[("traceless", "traceless")] == (2, 1)
    assert len(audit.cubic_tensor_basis) == 2
    assert len(audit.continuous_tensor_basis) == 1


def test_vector_and_tensor_reference_pairings() -> None:
    audit = build_audit()

    assert audit.vector_basis == (
        ("1", "0", "0"),
        ("0", "1", "0"),
        ("0", "0", "1"),
    )
    assert audit.continuous_tensor_basis[0] == (
        ("1", "1/2", "0", "0", "0"),
        ("1/2", "1", "0", "0", "0"),
        ("0", "0", "1", "0", "0"),
        ("0", "0", "0", "1", "0"),
        ("0", "0", "0", "0", "1"),
    )


def test_z4_conjugate_pair_reduces_multiplicity_freedom() -> None:
    audit = build_audit()

    assert audit.uncharged_pt_doublet_dimension == 2
    assert audit.conjugate_quarter_doublet_dimension == 1
    assert not audit.same_quarter_neutral
    assert audit.conjugate_quarter_neutral
