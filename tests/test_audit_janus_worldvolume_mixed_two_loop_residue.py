from __future__ import annotations

import sympy as sp

from scripts.audit_janus_worldvolume_mixed_two_loop_residue import build_audit


def test_mixed_sunset_pole_loses_gauge_mass_dependence() -> None:
    audit = build_audit()
    assert audit.sunset_remainder == "mEta2**2/4"
    assert audit.kappa4_residue == "0"
    assert audit.kappa2_lambda6_residue == "0"


def test_conditional_mixed_beta_coefficient() -> None:
    audit = build_audit()
    assert sp.simplify(sp.sympify(audit.conditional_ms_beta_coefficient) - 75 / (32 * sp.pi**2)) == 0
    assert audit.verdict == "conditional_on_candidate_euclidean_mcs_feynman_rules"


def test_composite_source_derivative_and_cs_coefficient() -> None:
    audit = build_audit()
    lambda6 = sp.symbols("lambda6")
    assert sp.simplify(sp.sympify(audit.composite_source_pole_residue) - 5 * lambda6 / (64 * sp.pi**2)) == 0
    assert sp.simplify(sp.sympify(audit.composite_anomalous_coefficient) - 5 / (16 * sp.pi**2)) == 0
    assert sp.simplify(sp.sympify(audit.non_ll_callan_symanzik_coefficient) - 445 / (32 * sp.pi**2)) == 0
