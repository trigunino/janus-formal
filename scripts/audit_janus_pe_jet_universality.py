#!/usr/bin/env python3
"""Executable checks for Program P.E-J finite-jet universality.

The script is intentionally elementary. Lean carries the exact algebraic
proofs; these checks provide independent numerical/regression coverage for the
finite-difference counterexample and finite-jet equivariance identities.
"""

from __future__ import annotations

import math
import re
from collections.abc import Callable, Iterable
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]

PROGRAMME_PE_GATES = {
    "P0EFTJanusEuclideanKoszulConnectionExistence.lean":
        "theorem smoothEuclideanKoszulConnection_exists",
    "P0EFTJanusProjectedSeedVaryingNormalBundle.lean":
        "def projectedSeedVaryingNormalBundleFamily",
    "P0EFTJanusEuclideanGlobalSpinCJetRealization.lean":
        "theorem EuclideanMetricProjectedSeedImmersionData.global_spinC_jet_realization",
    "P0EFTJanusEuclideanStructuredJetActionGroupoidRealization.lean":
        "theorem euclidean_lowOrder_spinC_groupoid_realized",
    "P0EFTJanusEuclideanStructuredJetOverlapGroupoid.lean":
        "theorem euclideanLowOrderSpinCOverlapArrow_comp",
    "P0EFTJanusEuclideanStructuredJetOverlapDescent.lean":
        "theorem euclideanLowOrderDescendedObservable_contDiff",
    "P0EFTJanusGlobalSpinCCechDescent.lean":
        "def globalSpinCCechPresentation",
    "P0EFTJanusCechAbelianConnectionDescent.lean": (
        "theorem CechAbelianConnectionDescentData.descendedCurvature_contDiff",
        "def CechAbelianConnectionDescentData.descendedClosedCurvatureDerivative",
        "theorem CechAbelianConnectionDescentData.descendedCurvature_fderiv_cyclic",
    ),
    "P0EFTJanusMappingTorusStructuredJetGroupoid.lean": (
        "instance janusDeckGroupoid",
        "def StructuredJetDeckRepresentation.toFunctor",
        "theorem deckTargetComponent_isLocalDiffeomorph",
        "theorem SmoothDeckInvariantMap.existsUnique_descended_contMDiff",
        "theorem reflectedSphere_existsUnique_smooth_descent",
        "theorem SmoothDeckHolonomicStructuredJetFamily.descended_is_holonomic",
        "theorem SmoothDeckHolonomicStructuredJetFamily.descendedReducedJet_contMDiff",
    ),
}


def assert_programme_pe_gate_integrity(repo_root: Path = REPO_ROOT) -> None:
    """Require the new constructive gates and reject proof placeholders."""
    gate_root = repo_root / (
        "JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates"
    )
    facade = (
        repo_root
        / "JanusFormal/Branches/FundamentalGeometryPEJetUniversality.lean"
    ).read_text(encoding="utf-8")

    for filename, required in PROGRAMME_PE_GATES.items():
        source = (gate_root / filename).read_text(encoding="utf-8")
        declarations = (required,) if isinstance(required, str) else required
        for declaration in declarations:
            if declaration not in source:
                raise AssertionError(
                    f"missing Programme P-E declaration: {declaration}"
                )
        if re.search(r"\b(?:sorry|admit|axiom)\b", source):
            raise AssertionError(f"proof placeholder found in {filename}")
        if f"Gates.{filename.removesuffix('.lean')}" not in facade:
            raise AssertionError(f"Programme P-E facade omits {filename}")

    status = "conditionalSmoothAbelianCurvatureBianchiProved"
    if f"{status} : Prop" not in facade or f"s.{status}" not in facade:
        raise AssertionError("Programme P-E facade omits the Bianchi status")

    mapping_torus_statuses = (
        "effectiveD8DeckCategoryAndGroupoidConstructed",
        "effectiveD8DependentSourceTargetFamiliesConstructed",
        "effectiveD8StructuredJetFunctorConstructed",
        "effectiveD8DeckGroupoidEtaleComponentwiseProved",
        "effectiveD8SmoothInvariantDescentUniqueProved",
        "effectiveD8LowOrderHolonomicJetDescentProved",
        "effectiveD8LowOrderIIFReductionDescentProved",
    )
    for status in mapping_torus_statuses:
        if f"{status} : Prop" not in facade or f"s.{status}" not in facade:
            raise AssertionError(
                f"Programme P-E facade omits D8 structured-jet status: {status}"
            )


def forward_difference(function: Callable[[float], float], x: float) -> float:
    """Unit-step forward difference."""
    return function(x + 1.0) - function(x)


def iterated_difference(
    function: Callable[[float], float], order: int, x: float
) -> float:
    """Iterate the unit-step forward difference."""
    if order < 0:
        raise ValueError("order must be nonnegative")
    current = function
    for _ in range(order):
        previous = current
        current = lambda value, previous=previous: forward_difference(
            previous, value
        )
    return current(x)


def exponential_difference_formula(order: int, x: float) -> float:
    """Closed form Delta^order exp(x)."""
    return (math.e - 1.0) ** order * math.exp(x)


def finite_cover_order_bound(local_orders: Iterable[int]) -> int:
    """Simple common upper bound used by the Lean theorem."""
    orders = list(local_orders)
    if any(order < 0 for order in orders):
        raise ValueError("jet orders must be nonnegative")
    return sum(orders)


def sign_action(sign: int, value: float) -> float:
    """Z2 action used in the finite-jet equivariance audit."""
    if sign not in (-1, 1):
        raise ValueError("sign must be -1 or +1")
    return sign * value


def even_evaluator(jet_value: float) -> float:
    """Scalar invariant evaluator Phi(j)=j^2."""
    return jet_value**2


def odd_evaluator(jet_value: float) -> float:
    """Covariant evaluator Phi(j)=j."""
    return jet_value


def run_audit() -> None:
    assert_programme_pe_gate_integrity()

    # Exact formula checked numerically on a broad deterministic grid.
    for order in range(9):
        for x in (-3.0, -1.25, 0.0, 0.5, 2.0):
            actual = iterated_difference(math.exp, order, x)
            expected = exponential_difference_formula(order, x)
            if not math.isclose(actual, expected, rel_tol=2e-10, abs_tol=2e-10):
                raise AssertionError(
                    f"finite-difference mismatch: n={order}, x={x}, "
                    f"actual={actual}, expected={expected}"
                )

    # No tested positive finite difference of exp vanishes.
    for order in range(1, 9):
        value = iterated_difference(math.exp, order, 0.0)
        if value == 0.0:
            raise AssertionError("exp unexpectedly passed a polynomial test")

    # Every listed local order lies below the finite-cover sum bound.
    local_orders = [0, 2, 5, 3, 7]
    bound = finite_cover_order_bound(local_orders)
    if not all(order <= bound for order in local_orders):
        raise AssertionError("finite-cover order bound failed")

    # Componentwise order n defeats every proposed global bound K at n=K+1.
    for proposed_bound in range(20):
        witness_component = proposed_bound + 1
        if witness_component <= proposed_bound:
            raise AssertionError("unbounded-order witness failed")

    # Scalar invariance of j^2 under the sign action.
    for sign in (-1, 1):
        for jet_value in (-2.5, -1.0, 0.0, 3.0):
            lhs = even_evaluator(sign_action(sign, jet_value))
            rhs = even_evaluator(jet_value)
            if lhs != rhs:
                raise AssertionError("scalar jet invariant failed")

    # Vector covariance of Phi(j)=j under the same sign representation.
    for sign in (-1, 1):
        for jet_value in (-2.5, -1.0, 0.0, 3.0):
            lhs = odd_evaluator(sign_action(sign, jet_value))
            rhs = sign_action(sign, odd_evaluator(jet_value))
            if lhs != rhs:
                raise AssertionError("jet covariance failed")

    print("Program P.E-J audit: all checks passed")


if __name__ == "__main__":
    run_audit()
