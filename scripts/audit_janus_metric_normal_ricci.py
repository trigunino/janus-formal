#!/usr/bin/env python3
"""Exact rational audit of the metric normal-connection Ricci identity.

The model uses an adapted Euclidean splitting ``T ⊕ N``.  For a tangent basis
vector ``e_i`` the connection block is

    Ω_i(t, ξ) = (-A_ξ e_i, II(e_i, t) + ω_i ξ).

The normal connection curvature is

    R_perp_ij = d_i ω_j - d_j ω_i + [ω_i, ω_j].

The audit computes the full block curvature

    R_amb_ij = d_i Ω_j - d_j Ω_i + [Ω_i, Ω_j]

and checks, exactly over ``fractions.Fraction``, that

    <R_perp_ij ξ, η>
      = <R_amb_ij ξ, η> + <[A_ξ, A_η] e_i, e_j>.

This is a finite-dimensional sign/convention audit.  It does not replace the
Lean proof or construct the manifold normal connection.
"""

from __future__ import annotations

from fractions import Fraction
from typing import TypeAlias

Scalar: TypeAlias = Fraction
Vector: TypeAlias = tuple[Scalar, ...]
Matrix: TypeAlias = tuple[tuple[Scalar, ...], ...]
SecondFundamentalForm: TypeAlias = tuple[Matrix, ...]


def shape(matrix: Matrix) -> tuple[int, int]:
    rows = len(matrix)
    columns = len(matrix[0]) if rows else 0
    if any(len(row) != columns for row in matrix):
        raise ValueError("matrix rows must have equal length")
    return rows, columns


def zero_matrix(rows: int, columns: int) -> Matrix:
    return tuple(tuple(Fraction(0) for _ in range(columns)) for _ in range(rows))


def identity_matrix(size: int) -> Matrix:
    return tuple(
        tuple(Fraction(int(row == column)) for column in range(size))
        for row in range(size)
    )


def matrix_add(first: Matrix, second: Matrix) -> Matrix:
    if shape(first) != shape(second):
        raise ValueError("matrix shapes must agree")
    return tuple(
        tuple(left + right for left, right in zip(first_row, second_row, strict=True))
        for first_row, second_row in zip(first, second, strict=True)
    )


def matrix_negate(matrix: Matrix) -> Matrix:
    return tuple(tuple(-entry for entry in row) for row in matrix)


def matrix_subtract(first: Matrix, second: Matrix) -> Matrix:
    return matrix_add(first, matrix_negate(second))


def transpose(matrix: Matrix) -> Matrix:
    rows, columns = shape(matrix)
    return tuple(
        tuple(matrix[row][column] for row in range(rows))
        for column in range(columns)
    )


def matrix_multiply(first: Matrix, second: Matrix) -> Matrix:
    first_rows, first_columns = shape(first)
    second_rows, second_columns = shape(second)
    if first_columns != second_rows:
        raise ValueError("inner matrix dimensions must agree")
    return tuple(
        tuple(
            sum(
                (first[row][index] * second[index][column]
                 for index in range(first_columns)),
                Fraction(0),
            )
            for column in range(second_columns)
        )
        for row in range(first_rows)
    )


def matrix_vector(matrix: Matrix, vector: Vector) -> Vector:
    rows, columns = shape(matrix)
    if columns != len(vector):
        raise ValueError("matrix/vector dimensions must agree")
    return tuple(
        sum((matrix[row][column] * vector[column] for column in range(columns)), Fraction(0))
        for row in range(rows)
    )


def dot(first: Vector, second: Vector) -> Scalar:
    if len(first) != len(second):
        raise ValueError("vector dimensions must agree")
    return sum((left * right for left, right in zip(first, second, strict=True)), Fraction(0))


def commutator(first: Matrix, second: Matrix) -> Matrix:
    return matrix_subtract(matrix_multiply(first, second), matrix_multiply(second, first))


def is_skew(matrix: Matrix) -> bool:
    return transpose(matrix) == matrix_negate(matrix)


def block_matrix(
    top_left: Matrix,
    top_right: Matrix,
    bottom_left: Matrix,
    bottom_right: Matrix,
) -> Matrix:
    tl_rows, tl_columns = shape(top_left)
    tr_rows, tr_columns = shape(top_right)
    bl_rows, bl_columns = shape(bottom_left)
    br_rows, br_columns = shape(bottom_right)
    if tl_rows != tr_rows or bl_rows != br_rows:
        raise ValueError("block row dimensions must agree")
    if tl_columns != bl_columns or tr_columns != br_columns:
        raise ValueError("block column dimensions must agree")
    return tuple(
        tuple(top_left[row]) + tuple(top_right[row]) for row in range(tl_rows)
    ) + tuple(
        tuple(bottom_left[row]) + tuple(bottom_right[row]) for row in range(bl_rows)
    )


def lower_right_block(matrix: Matrix, tangent_dimension: int) -> Matrix:
    rows, columns = shape(matrix)
    if rows != columns or tangent_dimension > rows:
        raise ValueError("expected a square block matrix")
    return tuple(
        tuple(row[tangent_dimension:]) for row in matrix[tangent_dimension:]
    )


def second_fundamental_block(
    second_fundamental: SecondFundamentalForm,
    tangent_index: int,
) -> Matrix:
    """Matrix ``B_i : T -> N`` with rows indexed by normal directions."""
    normal_dimension = len(second_fundamental)
    tangent_dimension = len(second_fundamental[0])
    return tuple(
        tuple(second_fundamental[normal][tangent_index][column]
              for column in range(tangent_dimension))
        for normal in range(normal_dimension)
    )


def shape_operator(
    second_fundamental: SecondFundamentalForm,
    normal: Vector,
) -> Matrix:
    normal_dimension = len(second_fundamental)
    if len(normal) != normal_dimension:
        raise ValueError("normal vector has the wrong dimension")
    tangent_dimension = len(second_fundamental[0])
    return tuple(
        tuple(
            sum(
                (normal[index] * second_fundamental[index][row][column]
                 for index in range(normal_dimension)),
                Fraction(0),
            )
            for column in range(tangent_dimension)
        )
        for row in range(tangent_dimension)
    )


def adapted_connection_block(
    second_fundamental: SecondFundamentalForm,
    normal_connection: Matrix,
    tangent_index: int,
) -> Matrix:
    tangent_dimension = len(second_fundamental[0])
    normal_dimension = len(second_fundamental)
    b_i = second_fundamental_block(second_fundamental, tangent_index)
    return block_matrix(
        zero_matrix(tangent_dimension, tangent_dimension),
        matrix_negate(transpose(b_i)),
        b_i,
        normal_connection,
    )


def adapted_connection_derivative_block(
    tangent_dimension: int,
    normal_derivative: Matrix,
) -> Matrix:
    normal_dimension, normal_columns = shape(normal_derivative)
    if normal_dimension != normal_columns:
        raise ValueError("normal derivative must be square")
    return block_matrix(
        zero_matrix(tangent_dimension, tangent_dimension),
        zero_matrix(tangent_dimension, normal_dimension),
        zero_matrix(normal_dimension, tangent_dimension),
        normal_derivative,
    )


def basis_vector(dimension: int, index: int) -> Vector:
    return tuple(Fraction(int(position == index)) for position in range(dimension))


def normal_curvature(
    omega_i: Matrix,
    omega_j: Matrix,
    derivative_ij: Matrix,
    derivative_ji: Matrix,
) -> Matrix:
    return matrix_add(
        matrix_subtract(derivative_ij, derivative_ji),
        commutator(omega_i, omega_j),
    )


def ambient_block_curvature(
    omega_i_block: Matrix,
    omega_j_block: Matrix,
    derivative_ij_block: Matrix,
    derivative_ji_block: Matrix,
) -> Matrix:
    return matrix_add(
        matrix_subtract(derivative_ij_block, derivative_ji_block),
        commutator(omega_i_block, omega_j_block),
    )


def ricci_shape_scalar(
    second_fundamental: SecondFundamentalForm,
    tangent_i: int,
    tangent_j: int,
    first_normal: Vector,
    second_normal: Vector,
) -> Scalar:
    first_shape = shape_operator(second_fundamental, first_normal)
    second_shape = shape_operator(second_fundamental, second_normal)
    shape_commutator = commutator(first_shape, second_shape)
    return shape_commutator[tangent_j][tangent_i]


def example_data() -> tuple[
    SecondFundamentalForm,
    tuple[Matrix, Matrix],
    tuple[Matrix, Matrix],
]:
    second_fundamental: SecondFundamentalForm = (
        (
            (Fraction(2), Fraction(1)),
            (Fraction(1), Fraction(-1)),
        ),
        (
            (Fraction(0), Fraction(3)),
            (Fraction(3), Fraction(4)),
        ),
        (
            (Fraction(-2), Fraction(5)),
            (Fraction(5), Fraction(1)),
        ),
    )
    omega_0: Matrix = (
        (Fraction(0), Fraction(1), Fraction(-2)),
        (Fraction(-1), Fraction(0), Fraction(3)),
        (Fraction(2), Fraction(-3), Fraction(0)),
    )
    omega_1: Matrix = (
        (Fraction(0), Fraction(-4), Fraction(1)),
        (Fraction(4), Fraction(0), Fraction(2)),
        (Fraction(-1), Fraction(-2), Fraction(0)),
    )
    derivative_01: Matrix = (
        (Fraction(0), Fraction(2), Fraction(-1)),
        (Fraction(-2), Fraction(0), Fraction(5)),
        (Fraction(1), Fraction(-5), Fraction(0)),
    )
    derivative_10: Matrix = (
        (Fraction(0), Fraction(-3), Fraction(4)),
        (Fraction(3), Fraction(0), Fraction(-2)),
        (Fraction(-4), Fraction(2), Fraction(0)),
    )
    return second_fundamental, (omega_0, omega_1), (derivative_01, derivative_10)


def run_audit() -> None:
    second_fundamental, omega, derivative = example_data()
    tangent_dimension = 2
    normal_dimension = 3

    assert all(matrix == transpose(matrix) for matrix in second_fundamental)
    assert all(is_skew(matrix) for matrix in omega)
    assert all(is_skew(matrix) for matrix in derivative)

    normal_r = normal_curvature(omega[0], omega[1], derivative[0], derivative[1])
    assert is_skew(normal_r)

    omega_block_0 = adapted_connection_block(second_fundamental, omega[0], 0)
    omega_block_1 = adapted_connection_block(second_fundamental, omega[1], 1)
    derivative_block_01 = adapted_connection_derivative_block(
        tangent_dimension, derivative[0]
    )
    derivative_block_10 = adapted_connection_derivative_block(
        tangent_dimension, derivative[1]
    )
    ambient_r = ambient_block_curvature(
        omega_block_0,
        omega_block_1,
        derivative_block_01,
        derivative_block_10,
    )
    ambient_normal_block = lower_right_block(ambient_r, tangent_dimension)
    assert is_skew(ambient_normal_block)

    for first_index in range(normal_dimension):
        first_normal = basis_vector(normal_dimension, first_index)
        for second_index in range(normal_dimension):
            second_normal = basis_vector(normal_dimension, second_index)
            normal_scalar = normal_r[second_index][first_index]
            ambient_scalar = ambient_normal_block[second_index][first_index]
            shape_scalar = ricci_shape_scalar(
                second_fundamental,
                0,
                1,
                first_normal,
                second_normal,
            )
            assert normal_scalar == ambient_scalar + shape_scalar

    first_normal = (Fraction(2), Fraction(-1), Fraction(3))
    second_normal = (Fraction(-2), Fraction(4), Fraction(1))
    normal_scalar = dot(matrix_vector(normal_r, first_normal), second_normal)
    ambient_scalar = dot(
        matrix_vector(ambient_normal_block, first_normal), second_normal
    )
    shape_scalar = ricci_shape_scalar(
        second_fundamental, 0, 1, first_normal, second_normal
    )
    assert normal_scalar == ambient_scalar + shape_scalar

    assert matrix_multiply(identity_matrix(tangent_dimension), shape_operator(
        second_fundamental, first_normal
    )) == shape_operator(second_fundamental, first_normal)

    print("Metric normal-connection Ricci audit: all exact checks passed")


if __name__ == "__main__":
    run_audit()
