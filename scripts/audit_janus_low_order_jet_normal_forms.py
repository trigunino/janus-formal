#!/usr/bin/env python3
"""Exact audits for the first low-order structured-jet normal forms.

The calculations use ``fractions.Fraction`` throughout. They verify concrete
linear-algebra statements mirrored by the Lean orbit theorems:

* after first-order normalization of an immersion, the second-order chain rule
  makes a quadratic source change remove the tangential part of the second jet
  while preserving the normal part;
* an abelian gauge two-jet removes the connection value and symmetric derivative
  while preserving the alternating curvature tensor;
* two abelian connection one-jets with equal curvature are related by the
  explicit gradient/Hessian gauge obtained from their difference.

These are low-order local models, not a construction of the full smooth Janus
SpinC jet groupoid.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import TypeAlias

Scalar: TypeAlias = Fraction
Vector: TypeAlias = tuple[Scalar, ...]
Matrix: TypeAlias = tuple[tuple[Scalar, ...], ...]
QuadraticTensor: TypeAlias = tuple[Matrix, ...]


def _matrix_shape(matrix: Matrix) -> tuple[int, int]:
    rows = len(matrix)
    columns = len(matrix[0]) if rows else 0
    if any(len(row) != columns for row in matrix):
        raise ValueError("matrix rows must have equal length")
    return rows, columns


def vector_add(first: Vector, second: Vector) -> Vector:
    if len(first) != len(second):
        raise ValueError("vector shapes must agree")
    return tuple(left + right for left, right in zip(first, second, strict=True))


def vector_negate(vector: Vector) -> Vector:
    return tuple(-entry for entry in vector)


def vector_subtract(first: Vector, second: Vector) -> Vector:
    return vector_add(first, vector_negate(second))


def matrix_add(first: Matrix, second: Matrix) -> Matrix:
    if _matrix_shape(first) != _matrix_shape(second):
        raise ValueError("matrix shapes must agree")
    return tuple(
        tuple(left + right for left, right in zip(first_row, second_row, strict=True))
        for first_row, second_row in zip(first, second, strict=True)
    )


def matrix_negate(matrix: Matrix) -> Matrix:
    return tuple(tuple(-entry for entry in row) for row in matrix)


def matrix_subtract(first: Matrix, second: Matrix) -> Matrix:
    return matrix_add(first, matrix_negate(second))


def matrix_scale(scale: Scalar, matrix: Matrix) -> Matrix:
    return tuple(tuple(scale * entry for entry in row) for row in matrix)


def transpose(matrix: Matrix) -> Matrix:
    rows, columns = _matrix_shape(matrix)
    if rows == 0:
        return ()
    return tuple(
        tuple(matrix[row][column] for row in range(rows))
        for column in range(columns)
    )


def zero_matrix(rows: int, columns: int) -> Matrix:
    return tuple(tuple(Fraction(0) for _ in range(columns)) for _ in range(rows))


def symmetric_part(matrix: Matrix) -> Matrix:
    rows, columns = _matrix_shape(matrix)
    if rows != columns:
        raise ValueError("symmetric decomposition requires a square matrix")
    return matrix_scale(Fraction(1, 2), matrix_add(matrix, transpose(matrix)))


def alternating_part(matrix: Matrix) -> Matrix:
    rows, columns = _matrix_shape(matrix)
    if rows != columns:
        raise ValueError("alternating decomposition requires a square matrix")
    return matrix_scale(
        Fraction(1, 2), matrix_add(matrix, matrix_negate(transpose(matrix)))
    )


def curvature_matrix(derivative: Matrix) -> Matrix:
    """Return ``F_ij = partial_i A_j - partial_j A_i``."""
    return matrix_add(derivative, matrix_negate(transpose(derivative)))


def is_symmetric(matrix: Matrix) -> bool:
    return matrix == transpose(matrix)


def is_alternating(matrix: Matrix) -> bool:
    return matrix == matrix_negate(transpose(matrix))


def tensor_add(first: QuadraticTensor, second: QuadraticTensor) -> QuadraticTensor:
    if len(first) != len(second):
        raise ValueError("quadratic-tensor target dimensions must agree")
    return tuple(
        matrix_add(left, right) for left, right in zip(first, second, strict=True)
    )


def tensor_negate(tensor: QuadraticTensor) -> QuadraticTensor:
    return tuple(matrix_negate(component) for component in tensor)


@dataclass(frozen=True)
class ImmersionSecondJet:
    """Quadratic jet split into tangent- and normal-valued components."""

    tangential: QuadraticTensor
    normal: QuadraticTensor


def source_quadratic_change(
    jet: ImmersionSecondJet, change: QuadraticTensor
) -> ImmersionSecondJet:
    """Normalized second-order chain rule for an identity-linear source jet."""
    return ImmersionSecondJet(
        tangential=tensor_add(jet.tangential, change),
        normal=jet.normal,
    )


def normalize_immersion_second_jet(
    jet: ImmersionSecondJet,
) -> tuple[ImmersionSecondJet, QuadraticTensor]:
    change = tensor_negate(jet.tangential)
    return source_quadratic_change(jet, change), change


@dataclass(frozen=True)
class AbelianConnectionOneJet:
    value: Vector
    derivative: Matrix


@dataclass(frozen=True)
class AbelianGaugeTwoJet:
    gradient: Vector
    hessian: Matrix


def apply_abelian_gauge_two_jet(
    jet: AbelianConnectionOneJet, gauge: AbelianGaugeTwoJet
) -> AbelianConnectionOneJet:
    if not is_symmetric(gauge.hessian):
        raise ValueError("an abelian gauge Hessian must be symmetric")
    return AbelianConnectionOneJet(
        value=vector_add(jet.value, gauge.gradient),
        derivative=matrix_add(jet.derivative, gauge.hessian),
    )


def normalize_abelian_connection_one_jet(
    jet: AbelianConnectionOneJet,
) -> tuple[AbelianConnectionOneJet, AbelianGaugeTwoJet]:
    gauge = AbelianGaugeTwoJet(
        gradient=vector_negate(jet.value),
        hessian=matrix_negate(symmetric_part(jet.derivative)),
    )
    return apply_abelian_gauge_two_jet(jet, gauge), gauge


def gauge_between_equal_curvatures(
    first: AbelianConnectionOneJet,
    second: AbelianConnectionOneJet,
) -> AbelianGaugeTwoJet:
    """Construct the unique formal gradient/Hessian difference gauge.

    Equality of curvature is exactly the condition that the derivative
    difference be symmetric, hence admissible as the Hessian of a scalar
    two-jet.
    """

    if len(first.value) != len(second.value):
        raise ValueError("connection-value dimensions must agree")
    if _matrix_shape(first.derivative) != _matrix_shape(second.derivative):
        raise ValueError("connection-derivative shapes must agree")
    if curvature_matrix(first.derivative) != curvature_matrix(second.derivative):
        raise ValueError("connection one-jets must have equal curvature")

    gauge = AbelianGaugeTwoJet(
        gradient=vector_subtract(second.value, first.value),
        hessian=matrix_subtract(second.derivative, first.derivative),
    )
    if not is_symmetric(gauge.hessian):
        raise AssertionError("equal curvature should force a symmetric difference")
    return gauge


def run_audit() -> None:
    immersion = ImmersionSecondJet(
        tangential=(
            (
                (Fraction(1), Fraction(2)),
                (Fraction(2), Fraction(-3)),
            ),
            (
                (Fraction(4), Fraction(-1)),
                (Fraction(-1), Fraction(5)),
            ),
        ),
        normal=(
            (
                (Fraction(7), Fraction(3, 2)),
                (Fraction(3, 2), Fraction(-2)),
            ),
        ),
    )
    normalized_immersion, immersion_change = normalize_immersion_second_jet(
        immersion
    )
    expected_zero_tangent = tuple(
        zero_matrix(*_matrix_shape(component)) for component in immersion.tangential
    )
    assert normalized_immersion.tangential == expected_zero_tangent
    assert normalized_immersion.normal == immersion.normal
    assert source_quadratic_change(immersion, immersion_change) == normalized_immersion

    connection = AbelianConnectionOneJet(
        value=(Fraction(2), Fraction(-3), Fraction(5, 2)),
        derivative=(
            (Fraction(1), Fraction(4), Fraction(-2)),
            (Fraction(-1), Fraction(3), Fraction(7)),
            (Fraction(5), Fraction(0), Fraction(-4)),
        ),
    )
    original_curvature = curvature_matrix(connection.derivative)
    normalized_connection, normalizing_gauge = normalize_abelian_connection_one_jet(
        connection
    )
    assert normalized_connection.value == (Fraction(0), Fraction(0), Fraction(0))
    assert symmetric_part(normalized_connection.derivative) == zero_matrix(3, 3)
    assert normalized_connection.derivative == alternating_part(connection.derivative)
    assert curvature_matrix(normalized_connection.derivative) == original_curvature
    assert is_symmetric(normalizing_gauge.hessian)

    arbitrary_symmetric_hessian = (
        (Fraction(3), Fraction(1), Fraction(-2)),
        (Fraction(1), Fraction(4), Fraction(5)),
        (Fraction(-2), Fraction(5), Fraction(-6)),
    )
    arbitrary_gauge = AbelianGaugeTwoJet(
        gradient=(Fraction(11), Fraction(-8), Fraction(2)),
        hessian=arbitrary_symmetric_hessian,
    )
    transformed = apply_abelian_gauge_two_jet(connection, arbitrary_gauge)
    assert curvature_matrix(transformed.derivative) == original_curvature
    assert is_alternating(original_curvature)

    reconstructed_gauge = gauge_between_equal_curvatures(connection, transformed)
    assert reconstructed_gauge == arbitrary_gauge
    assert apply_abelian_gauge_two_jet(connection, reconstructed_gauge) == transformed

    print("Low-order structured-jet normal-form audit: all checks passed")


if __name__ == "__main__":
    run_audit()
