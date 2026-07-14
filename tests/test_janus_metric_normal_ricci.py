from __future__ import annotations

from fractions import Fraction

from scripts.audit_janus_metric_normal_ricci import (
    adapted_connection_block,
    adapted_connection_derivative_block,
    ambient_block_curvature,
    basis_vector,
    commutator,
    dot,
    example_data,
    is_skew,
    lower_right_block,
    matrix_vector,
    normal_curvature,
    ricci_shape_scalar,
    shape_operator,
)


def test_normal_connection_curvature_is_skew() -> None:
    _, omega, derivative = example_data()
    curvature = normal_curvature(omega[0], omega[1], derivative[0], derivative[1])
    assert is_skew(curvature)


def test_block_curvature_satisfies_ricci_on_basis_normals() -> None:
    second_fundamental, omega, derivative = example_data()
    tangent_dimension = 2
    normal_dimension = 3

    connection_0 = adapted_connection_block(second_fundamental, omega[0], 0)
    connection_1 = adapted_connection_block(second_fundamental, omega[1], 1)
    derivative_01 = adapted_connection_derivative_block(
        tangent_dimension, derivative[0]
    )
    derivative_10 = adapted_connection_derivative_block(
        tangent_dimension, derivative[1]
    )

    ambient_curvature = ambient_block_curvature(
        connection_0, connection_1, derivative_01, derivative_10
    )
    ambient_normal = lower_right_block(ambient_curvature, tangent_dimension)
    normal = normal_curvature(omega[0], omega[1], derivative[0], derivative[1])

    for first_index in range(normal_dimension):
        first_normal = basis_vector(normal_dimension, first_index)
        for second_index in range(normal_dimension):
            second_normal = basis_vector(normal_dimension, second_index)
            assert normal[second_index][first_index] == (
                ambient_normal[second_index][first_index]
                + ricci_shape_scalar(
                    second_fundamental,
                    0,
                    1,
                    first_normal,
                    second_normal,
                )
            )


def test_block_curvature_satisfies_ricci_on_general_normals() -> None:
    second_fundamental, omega, derivative = example_data()
    tangent_dimension = 2

    connection_0 = adapted_connection_block(second_fundamental, omega[0], 0)
    connection_1 = adapted_connection_block(second_fundamental, omega[1], 1)
    derivative_01 = adapted_connection_derivative_block(
        tangent_dimension, derivative[0]
    )
    derivative_10 = adapted_connection_derivative_block(
        tangent_dimension, derivative[1]
    )

    ambient_normal = lower_right_block(
        ambient_block_curvature(
            connection_0, connection_1, derivative_01, derivative_10
        ),
        tangent_dimension,
    )
    normal = normal_curvature(omega[0], omega[1], derivative[0], derivative[1])

    first_normal = (Fraction(2), Fraction(-1), Fraction(3))
    second_normal = (Fraction(-2), Fraction(4), Fraction(1))

    assert dot(matrix_vector(normal, first_normal), second_normal) == (
        dot(matrix_vector(ambient_normal, first_normal), second_normal)
        + ricci_shape_scalar(
            second_fundamental,
            0,
            1,
            first_normal,
            second_normal,
        )
    )


def test_shape_commutator_is_skew_in_normal_arguments() -> None:
    second_fundamental, _, _ = example_data()
    first_normal = (Fraction(1), Fraction(2), Fraction(-1))
    second_normal = (Fraction(3), Fraction(-2), Fraction(4))

    first_second = ricci_shape_scalar(
        second_fundamental, 0, 1, first_normal, second_normal
    )
    second_first = ricci_shape_scalar(
        second_fundamental, 0, 1, second_normal, first_normal
    )
    assert second_first == -first_second


def test_shape_operator_is_symmetric() -> None:
    second_fundamental, _, _ = example_data()
    normal = (Fraction(2), Fraction(-1), Fraction(3))
    shape = shape_operator(second_fundamental, normal)
    assert shape[0][1] == shape[1][0]
    assert commutator(shape, shape) == ((Fraction(0), Fraction(0)),
                                        (Fraction(0), Fraction(0)))
