from __future__ import annotations

from scripts.derive_janus_worldvolume_background_vertices import build_audit


def test_background_expansion_reconstructs_exact_inverse_square() -> None:
    audit = build_audit()
    assert audit.reconstruction_exact
    assert audit.coefficients == {
        "F2": "v**(-2)",
        "eta_F2": "-2/v**3",
        "eta2_F2": "3/v**4",
    }


def test_background_vertices_keep_density_dimension_three() -> None:
    audit = build_audit()
    assert audit.all_vertex_densities_dimension_three
    assert audit.verdict.endswith("one_loop_bookkeeping")
