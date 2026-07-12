from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp

# `python scripts/audit_janus_pe_spinor_pairings.py` places `scripts/` itself on
# `sys.path`, while pytest imports this file as `scripts.<module>` from the
# repository root. Support both execution modes without requiring `scripts` to
# be an installed package.
try:
    from scripts.audit_janus_pe_invariant_pairings import (
        _invariant_bilinear_basis,
        _matrix_as_strings,
    )
except ModuleNotFoundError:
    from audit_janus_pe_invariant_pairings import (  # type: ignore[no-redef]
        _invariant_bilinear_basis,
        _matrix_as_strings,
    )


@dataclass(frozen=True)
class PESpinorPairingAudit:
    complex_bilinear_dimension: int
    hermitian_dimension: int
    scalar_spinor_dimension: int
    complex_bilinear_basis: tuple[tuple[tuple[str, ...], ...], ...]
    hermitian_basis: tuple[tuple[tuple[str, ...], ...], ...]
    all_checks_pass: bool
    conclusion: str


def build_audit() -> PESpinorPairingAudit:
    imaginary = sp.I

    # Two quaternionic generators and one generic exact SU(2) element.
    spin_z = sp.diag(imaginary, -imaginary)
    spin_x = sp.Matrix([[0, imaginary], [imaginary, 0]])
    half = sp.Rational(1, 2)
    generic_spin = sp.Matrix(
        [
            [half + imaginary * half, half + imaginary * half],
            [-half + imaginary * half, half - imaginary * half],
        ]
    )
    generators = (spin_z, spin_x, generic_spin)

    complex_bilinear_basis = _invariant_bilinear_basis(generators, generators)
    hermitian_basis = _invariant_bilinear_basis(
        tuple(generator.conjugate() for generator in generators),
        generators,
    )
    scalar_spinor_basis = _invariant_bilinear_basis(
        tuple(sp.eye(1) for _ in generators), generators
    )

    epsilon = sp.Matrix([[0, -1], [1, 0]])
    identity = sp.eye(2)
    checks = [
        all(sp.simplify(generator.det() - 1) == 0 for generator in generators),
        all(
            sp.simplify(generator.conjugate().T * generator - identity)
            == sp.zeros(2)
            for generator in generators
        ),
        len(complex_bilinear_basis) == 1,
        complex_bilinear_basis[0] == epsilon,
        len(hermitian_basis) == 1,
        hermitian_basis[0] == identity,
        len(scalar_spinor_basis) == 0,
    ]

    return PESpinorPairingAudit(
        complex_bilinear_dimension=len(complex_bilinear_basis),
        hermitian_dimension=len(hermitian_basis),
        scalar_spinor_dimension=len(scalar_spinor_basis),
        complex_bilinear_basis=tuple(
            _matrix_as_strings(matrix) for matrix in complex_bilinear_basis
        ),
        hermitian_basis=tuple(
            _matrix_as_strings(matrix) for matrix in hermitian_basis
        ),
        all_checks_pass=all(checks),
        conclusion=(
            "The fundamental Spin(3)=SU(2) spinor has one invariant complex "
            "bilinear form, the antisymmetric epsilon tensor, and one invariant "
            "Hermitian form, the identity metric, each up to scale. There is no "
            "invariant scalar-spinor linear pairing. The symmetry type of the "
            "bilinear must still be combined with Grassmann parity, U(1) charge "
            "and the normal-root Z4 selection rule."
        ),
    )


def main() -> None:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    if not audit.all_checks_pass:
        raise SystemExit("Program P.E spinor-pairing audit failed")


if __name__ == "__main__":
    main()
