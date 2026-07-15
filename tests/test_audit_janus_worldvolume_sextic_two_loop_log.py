from __future__ import annotations

from scripts.audit_janus_worldvolume_sextic_two_loop_log import build_audit


def test_two_loop_six_point_topology_is_logarithmic() -> None:
    audit = build_audit()
    assert audit.loops == 2
    assert audit.internal_edges == 3
    assert audit.superficial_degree_d3 == 0
    assert audit.logarithmic_topology_identified


def test_dimensional_continuation_and_beta_relation_are_explicit() -> None:
    audit = build_audit()
    assert audit.coupling_dimension_near_d3 == "4*epsilon"
    assert audit.ms_beta_relation.startswith("beta_lambda6 = 4*A")
    assert audit.master_integral_pole_residue == "1/(64*pi**2)"
    assert audit.pole_residue_computed
    assert audit.repository_combinatorial_weight == "200"
    assert audit.standard_normalization_weight == "5/3"
    assert audit.pure_scalar_beta_coefficient == "25/(2*pi**2)"
    assert audit.standard_beta_coefficient == "5/(48*pi**2)"
    assert audit.literature_normalization_crosscheck
    assert audit.beta_coefficient_computed
