from __future__ import annotations

from scripts.audit_janus_pe_spinor_pairings import build_audit


def test_spinor_pairing_dimensions() -> None:
    audit = build_audit()

    assert audit.all_checks_pass
    assert audit.complex_bilinear_dimension == 1
    assert audit.hermitian_dimension == 1
    assert audit.scalar_spinor_dimension == 0


def test_spinor_reference_pairings() -> None:
    audit = build_audit()

    assert audit.complex_bilinear_basis == (
        (("0", "-1"), ("1", "0")),
    )
    assert audit.hermitian_basis == (
        (("1", "0"), ("0", "1")),
    )
