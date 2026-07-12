from __future__ import annotations

from scripts.audit_janus_d7_seeley_dewitt import (
    build_audit,
    reduced_dirac_coefficients,
)


def test_universal_and_product_throat_coefficients_agree() -> None:
    audit = build_audit()

    assert audit.all_checks_pass
    assert audit.symbolic_a0_residual == "0"
    assert audit.symbolic_a2_residual == "0"
    assert audit.symbolic_a4_residual == "0"
    assert audit.universal_to_dirac_a4_residual == "0"
    assert audit.local_coefficients_linear_in_circle_modulus


def test_small_time_spectrum_recovers_a0_a2_a4() -> None:
    audit = build_audit()

    assert audit.maximum_small_time_residual < 1.0e-7
    assert audit.smallest_time_extracted_a4_error < 1.0e-3
    assert len(audit.heat_trace_samples) == 5
    assert audit.heat_trace_samples[-1].absolute_residual < (
        audit.heat_trace_samples[0].absolute_residual
    )


def test_common_metric_cutoff_rescaling_leaves_local_action_invariant() -> None:
    audit = build_audit()

    assert audit.common_scale_orbit_residual < 1.0e-10


def test_primitive_monopole_a4_is_positive() -> None:
    _, _, a4 = reduced_dirac_coefficients(1.3, 4.2, 1)

    assert a4 > 0.0
