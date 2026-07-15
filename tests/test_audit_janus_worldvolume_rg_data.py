from __future__ import annotations

import math

import pytest

from scripts.audit_janus_worldvolume_rg_data import build_audit


def test_missing_microscopic_rg_data_blocks_closure() -> None:
    audit = build_audit()
    assert not audit.microscopic_inputs_supplied
    assert not audit.locally_stable_one_log_vacuum
    assert audit.verdict == "blocked_on_microscopic_beta_and_anomalous_dimension"


def test_positive_cs_coefficient_gives_conditional_local_vacuum() -> None:
    audit = build_audit(
        sextic_beta=0.2,
        composite_anomalous_dimension=0.01,
        sextic_coupling=0.5,
    )
    assert audit.log_coefficient == pytest.approx(0.185)
    assert audit.locally_stable_one_log_vacuum
    assert audit.callan_symanzik_residual == pytest.approx(0.0)
    assert audit.finite_scheme_residual == pytest.approx(0.0)


def test_nonpositive_cs_coefficient_rejects_local_stability() -> None:
    audit = build_audit(
        sextic_beta=0.01,
        composite_anomalous_dimension=0.1,
        sextic_coupling=1.0,
    )
    assert not audit.locally_stable_one_log_vacuum


def test_nonfinite_rg_input_is_rejected() -> None:
    with pytest.raises(ValueError):
        build_audit(
            sextic_beta=math.inf,
            composite_anomalous_dimension=0.0,
            sextic_coupling=1.0,
        )


def test_beta_sector_decomposition_is_audited() -> None:
    audit = build_audit(
        sextic_beta=0.23,
        pure_scalar_beta=0.2,
        mixed_gauge_scalar_beta=0.04,
        ll_beta=-0.01,
        composite_anomalous_dimension=0.01,
        sextic_coupling=0.5,
    )
    assert audit.beta_decomposition_residual == pytest.approx(0.0)
    assert audit.beta_decomposition_consistent


def test_inconsistent_beta_decomposition_blocks_vacuum_verdict() -> None:
    audit = build_audit(
        sextic_beta=0.3,
        pure_scalar_beta=0.2,
        mixed_gauge_scalar_beta=0.04,
        ll_beta=-0.01,
        composite_anomalous_dimension=0.0,
        sextic_coupling=0.5,
    )
    assert not audit.beta_decomposition_consistent
    assert not audit.locally_stable_one_log_vacuum
    assert audit.verdict == "inconsistent_beta_sector_decomposition"
