from __future__ import annotations

import math

from scripts.audit_janus_corrected_mcs_alpha import build_audit


def test_unit_level_corrected_mcs_scale() -> None:
    audit = build_audit()

    assert math.isclose(audit.charge_amplitude, 1.0 / (2.0 * math.pi))
    assert 4.0e-26 < audit.rg_invariant_mass_inverse_m < 5.0e-26
    assert 8.0e-33 < audit.rg_invariant_energy_eV < 1.0e-32
    assert 1.8 < audit.corrected_exponent_sum < 1.9
    assert audit.old_exact_cancellation_residual < -5.0
    assert 138.0 < audit.planck_to_rg_log_hierarchy < 142.0


def test_level_scaling() -> None:
    level_one = build_audit(chern_simons_level=1)
    level_two = build_audit(chern_simons_level=2)

    assert math.isclose(
        level_two.charge_amplitude,
        2.0 * level_one.charge_amplitude,
    )
    assert math.isclose(
        level_two.rg_invariant_mass_inverse_m,
        level_one.rg_invariant_mass_inverse_m / 2.0,
    )


def test_invalid_inputs_are_rejected() -> None:
    for kwargs in [
        {"target_alpha_squared_length_m": 0.0},
        {"chern_simons_level": 0},
        {"planck_length_m": 0.0},
    ]:
        try:
            build_audit(**kwargs)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid input should raise ValueError")
