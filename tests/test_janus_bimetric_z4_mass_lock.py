from __future__ import annotations

import math

from scripts.audit_janus_bimetric_z4_mass_lock import build_audit


def test_standard_and_doubled_spin_two_weight_counts() -> None:
    audit = build_audit()

    assert audit.all_checks_pass
    assert audit.standard_discriminant < 0
    assert audit.doubled_discriminant == 4
    assert math.isclose(audit.doubled_stationary_radials[0], 0.5)
    assert math.isclose(audit.doubled_stationary_radials[1], 1.0 / 3.0)
    assert math.isclose(audit.stable_dimensionless_exponent, math.log(3.0))


def test_mass_radius_compatibility_requires_light_mode() -> None:
    audit = build_audit()

    expected = math.log(3.0) / (math.sqrt(2.0) * math.pi)
    assert math.isclose(
        audit.compatible_mass_times_length,
        expected,
        rel_tol=1.0e-15,
    )
    assert audit.compatible_mass_times_length_squared < 0.5
    assert not audit.first_sphere_mass_compatible
    assert audit.diagnostic_mass_inverse_m_for_A_1e26m > 0.0
    assert audit.diagnostic_mass_eV_for_A_1e26m > 0.0


def test_minimal_five_mode_anomaly_cancels_across_pt_pair() -> None:
    audit = build_audit()

    assert audit.minimal_per_fold_periodic_weight == 1
    assert audit.minimal_per_fold_quarter_weight == 5
    assert audit.positive_fold_doubled_level == 1
    assert audit.negative_fold_doubled_level == -1
    assert audit.paired_level_sum == 0
