from __future__ import annotations

from scripts.audit_janus_twisted_hopf_geometry import build_audit


def test_twisted_hopf_geometry_audit() -> None:
    audit = build_audit()

    assert audit.all_checks_pass
    assert audit.euler_characteristic == 0
    assert audit.orientation_double_cover == "S3 x S1"
    assert audit.throat_topology.startswith("S2 x S1")
    assert audit.geometric_deck_group == "Z2"
    assert audit.pin_lift_group.startswith("Z4")
    assert 130.0 < audit.logarithmic_tunnel_period < 150.0
    assert 0.0 < audit.quotient_contraction < 1.0e-60
    assert 0.0 < audit.orientation_cover_contraction < 1.0e-120


def test_twisted_hopf_geometry_rejects_nonpositive_lengths() -> None:
    for alpha, uv in [(0.0, 1.0), (1.0, 0.0), (-1.0, 1.0)]:
        try:
            build_audit(alpha_squared_length_m=alpha, uv_length_m=uv)
        except ValueError:
            pass
        else:
            raise AssertionError("nonpositive lengths must be rejected")
