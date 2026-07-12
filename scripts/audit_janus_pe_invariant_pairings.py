from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class PairingDimension:
    left: str
    right: str
    cubic_dimension: int
    continuous_o3_dimension: int


@dataclass(frozen=True)
class PEInvariantPairingAudit:
    pairing_dimensions: tuple[PairingDimension, ...]
    cubic_tensor_basis: tuple[tuple[tuple[str, ...], ...], ...]
    continuous_tensor_basis: tuple[tuple[tuple[str, ...], ...], ...]
    vector_basis: tuple[tuple[str, ...], ...]
    uncharged_pt_doublet_dimension: int
    conjugate_quarter_doublet_dimension: int
    same_quarter_neutral: bool
    conjugate_quarter_neutral: bool
    all_checks_pass: bool
    conclusion: str


def _traceless_tensor_representation(rotation: sp.Matrix) -> sp.Matrix:
    """Induced action on coordinates (a,b,xy,xz,yz).

    The associated symmetric traceless matrix is

        [[a,  xy,      xz],
         [xy, b,       yz],
         [xz, yz, -a - b]].
    """

    a, b, xy, xz, yz = sp.symbols("a b xy xz yz")
    coordinates = (a, b, xy, xz, yz)
    tensor = sp.Matrix(
        [
            [a, xy, xz],
            [xy, b, yz],
            [xz, yz, -a - b],
        ]
    )
    transformed = sp.expand(rotation * tensor * rotation.T)
    transformed_coordinates = (
        transformed[0, 0],
        transformed[1, 1],
        transformed[0, 1],
        transformed[0, 2],
        transformed[1, 2],
    )
    return sp.Matrix(
        [
            [sp.diff(expression, coordinate) for coordinate in coordinates]
            for expression in transformed_coordinates
        ]
    )


def _invariant_bilinear_basis(
    left_representations: tuple[sp.Matrix, ...],
    right_representations: tuple[sp.Matrix, ...],
) -> tuple[sp.Matrix, ...]:
    if len(left_representations) != len(right_representations):
        raise ValueError("left and right generator lists must have the same length")
    if not left_representations:
        raise ValueError("at least one generator is required")

    left_dimension = left_representations[0].rows
    right_dimension = right_representations[0].rows
    variables = sp.symbols(f"b0:{left_dimension * right_dimension}")
    bilinear = sp.Matrix(left_dimension, right_dimension, variables)

    equations: list[sp.Expr] = []
    for left, right in zip(left_representations, right_representations, strict=True):
        residual = sp.expand(left.T * bilinear * right - bilinear)
        equations.extend(list(residual))

    coefficient_matrix, _ = sp.linear_eq_to_matrix(equations, variables)
    return tuple(
        sp.Matrix(left_dimension, right_dimension, vector)
        for vector in coefficient_matrix.nullspace()
    )


def _matrix_as_strings(matrix: sp.Matrix) -> tuple[tuple[str, ...], ...]:
    return tuple(
        tuple(str(sp.simplify(matrix[row, column])) for column in range(matrix.cols))
        for row in range(matrix.rows)
    )


def _symmetric_doublet_dimension(
    transformation: sp.Matrix,
    charge_transformation: sp.Matrix | None = None,
) -> int:
    a, b, c = sp.symbols("a b c")
    bilinear = sp.Matrix([[a, b], [b, c]])
    equations = list(sp.expand(transformation.T * bilinear * transformation - bilinear))
    if charge_transformation is not None:
        equations.extend(
            list(
                sp.expand(
                    charge_transformation.T * bilinear * charge_transformation
                    - bilinear
                )
            )
        )
    coefficient_matrix, _ = sp.linear_eq_to_matrix(equations, (a, b, c))
    return 3 - coefficient_matrix.rank()


def build_audit() -> PEInvariantPairingAudit:
    one = sp.eye(1)

    flip_x = sp.diag(-1, 1, 1)
    flip_y = sp.diag(1, -1, 1)
    swap_xy = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
    swap_yz = sp.Matrix([[1, 0, 0], [0, 0, 1], [0, 1, 0]])
    cubic_generators = (flip_x, flip_y, swap_xy, swap_yz)

    cosine = sp.Rational(3, 5)
    sine = sp.Rational(4, 5)
    rotate_z = sp.Matrix(
        [[cosine, -sine, 0], [sine, cosine, 0], [0, 0, 1]]
    )
    rotate_y = sp.Matrix(
        [[cosine, 0, sine], [0, 1, 0], [-sine, 0, cosine]]
    )
    continuous_generators = (rotate_z, rotate_y, flip_x)

    cubic_scalar = tuple(one for _ in cubic_generators)
    continuous_scalar = tuple(one for _ in continuous_generators)
    cubic_tensor = tuple(
        _traceless_tensor_representation(generator)
        for generator in cubic_generators
    )
    continuous_tensor = tuple(
        _traceless_tensor_representation(generator)
        for generator in continuous_generators
    )

    representation_pairs = (
        ("scalar", "scalar", cubic_scalar, cubic_scalar, continuous_scalar, continuous_scalar),
        ("scalar", "vector", cubic_scalar, cubic_generators, continuous_scalar, continuous_generators),
        ("scalar", "traceless", cubic_scalar, cubic_tensor, continuous_scalar, continuous_tensor),
        ("vector", "vector", cubic_generators, cubic_generators, continuous_generators, continuous_generators),
        ("vector", "traceless", cubic_generators, cubic_tensor, continuous_generators, continuous_tensor),
        ("traceless", "traceless", cubic_tensor, cubic_tensor, continuous_tensor, continuous_tensor),
    )

    pairing_dimensions: list[PairingDimension] = []
    bases: dict[tuple[str, str, str], tuple[sp.Matrix, ...]] = {}
    for left_name, right_name, cubic_left, cubic_right, full_left, full_right in representation_pairs:
        cubic_basis = _invariant_bilinear_basis(cubic_left, cubic_right)
        full_basis = _invariant_bilinear_basis(full_left, full_right)
        pairing_dimensions.append(
            PairingDimension(
                left=left_name,
                right=right_name,
                cubic_dimension=len(cubic_basis),
                continuous_o3_dimension=len(full_basis),
            )
        )
        bases[(left_name, right_name, "cubic")] = cubic_basis
        bases[(left_name, right_name, "continuous")] = full_basis

    vector_basis = bases[("vector", "vector", "continuous")]
    cubic_tensor_basis = bases[("traceless", "traceless", "cubic")]
    continuous_tensor_basis = bases[("traceless", "traceless", "continuous")]

    pt_exchange = sp.Matrix([[0, 1], [1, 0]])
    quarter_charge = sp.diag(sp.I, -sp.I)
    uncharged_pt_dimension = _symmetric_doublet_dimension(pt_exchange)
    conjugate_quarter_dimension = _symmetric_doublet_dimension(
        pt_exchange, quarter_charge
    )

    dimension_map = {
        (entry.left, entry.right): (
            entry.cubic_dimension,
            entry.continuous_o3_dimension,
        )
        for entry in pairing_dimensions
    }
    checks = [
        dimension_map[("scalar", "scalar")] == (1, 1),
        dimension_map[("scalar", "vector")] == (0, 0),
        dimension_map[("scalar", "traceless")] == (0, 0),
        dimension_map[("vector", "vector")] == (1, 1),
        dimension_map[("vector", "traceless")] == (0, 0),
        dimension_map[("traceless", "traceless")] == (2, 1),
        len(vector_basis) == 1 and vector_basis[0] == sp.eye(3),
        len(continuous_tensor_basis) == 1,
        continuous_tensor_basis[0]
        == sp.Matrix(
            [
                [1, sp.Rational(1, 2), 0, 0, 0],
                [sp.Rational(1, 2), 1, 0, 0, 0],
                [0, 0, 1, 0, 0],
                [0, 0, 0, 1, 0],
                [0, 0, 0, 0, 1],
            ]
        ),
        uncharged_pt_dimension == 2,
        conjugate_quarter_dimension == 1,
        (1 + 1) % 4 != 0,
        (1 + 3) % 4 == 0,
    ]

    return PEInvariantPairingAudit(
        pairing_dimensions=tuple(pairing_dimensions),
        cubic_tensor_basis=tuple(
            _matrix_as_strings(matrix) for matrix in cubic_tensor_basis
        ),
        continuous_tensor_basis=tuple(
            _matrix_as_strings(matrix) for matrix in continuous_tensor_basis
        ),
        vector_basis=_matrix_as_strings(vector_basis[0]),
        uncharged_pt_doublet_dimension=uncharged_pt_dimension,
        conjugate_quarter_doublet_dimension=conjugate_quarter_dimension,
        same_quarter_neutral=False,
        conjugate_quarter_neutral=True,
        all_checks_pass=all(checks),
        conclusion=(
            "Discrete signed permutations already force the vector metric and "
            "forbid scalar-vector/scalar-traceless/vector-traceless pairings, "
            "but leave two traceless-tensor norms. Adding generic exact O(3) "
            "rotations collapses the tensor pairing space to the Frobenius form. "
            "The conjugate Z4 quarter doublet has one neutral quadratic pairing, "
            "whereas an uncharged PT doublet retains two coefficients."
        ),
    )


def main() -> None:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    if not audit.all_checks_pass:
        raise SystemExit("Program P.E invariant-pairing audit failed")


if __name__ == "__main__":
    main()
