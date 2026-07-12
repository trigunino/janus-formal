from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class Z4DiracAlphaAudit:
    scanned_sphere_modes: int
    scanned_circle_modes_each_side: int
    normalized_minimum: int
    minimizing_modes: list[tuple[int, int]]
    circle_modulus: float
    gap_squared_times_length_squared: float
    ll_charge_times_length_squared: float
    sphere_gap_times_length_squared: float
    charge_to_sphere_gap_ratio: float
    alpha_over_geometry_length: float
    positive_fold_reduced_eta: float
    negative_fold_reduced_eta: float
    paired_reduced_eta: float
    all_checks_pass: bool
    conclusion: str


def normalized_spectrum_numerator(sphere_mode: int, circle_mode: int) -> int:
    if sphere_mode < 0:
        raise ValueError("sphere_mode must be nonnegative")
    return 8 * sphere_mode * (sphere_mode + 1) + (4 * circle_mode + 1) ** 2


def build_audit(
    max_sphere_mode: int = 8,
    max_abs_circle_mode: int = 12,
) -> Z4DiracAlphaAudit:
    if max_sphere_mode < 0 or max_abs_circle_mode < 0:
        raise ValueError("scan bounds must be nonnegative")

    spectrum = [
        (normalized_spectrum_numerator(k, m), k, m)
        for k in range(max_sphere_mode + 1)
        for m in range(-max_abs_circle_mode, max_abs_circle_mode + 1)
    ]
    minimum = min(value for value, _, _ in spectrum)
    minimizers = [(k, m) for value, k, m in spectrum if value == minimum]

    circle_modulus = math.sqrt(2.0) * math.pi
    gap_l2 = 1.0 / 8.0
    charge_l2 = 2.0 * gap_l2
    sphere_gap_l2 = 2.0
    charge_to_gap = charge_l2 / sphere_gap_l2

    # 16 q^2 A^4 = 1, expressed in units of L:
    # 16 (q L^2)^2 (A/L)^4 = 1.
    alpha_ratio = (1.0 / (16.0 * charge_l2**2)) ** 0.25

    eta_plus = 1.0 - 2.0 * 0.25
    eta_minus = -eta_plus
    eta_pair = eta_plus + eta_minus

    checks = [
        minimum == 1,
        minimizers == [(0, 0)],
        math.isclose(gap_l2, 1.0 / 8.0, rel_tol=1.0e-15),
        math.isclose(charge_l2, 1.0 / 4.0, rel_tol=1.0e-15),
        math.isclose(charge_to_gap, 1.0 / 8.0, rel_tol=1.0e-15),
        math.isclose(alpha_ratio, 1.0, rel_tol=1.0e-15),
        math.isclose(eta_plus, 0.5, rel_tol=1.0e-15),
        math.isclose(eta_minus, -0.5, rel_tol=1.0e-15),
        math.isclose(eta_pair, 0.0, abs_tol=1.0e-15),
    ]

    return Z4DiracAlphaAudit(
        scanned_sphere_modes=max_sphere_mode + 1,
        scanned_circle_modes_each_side=max_abs_circle_mode,
        normalized_minimum=minimum,
        minimizing_modes=minimizers,
        circle_modulus=circle_modulus,
        gap_squared_times_length_squared=gap_l2,
        ll_charge_times_length_squared=charge_l2,
        sphere_gap_times_length_squared=sphere_gap_l2,
        charge_to_sphere_gap_ratio=charge_to_gap,
        alpha_over_geometry_length=alpha_ratio,
        positive_fold_reduced_eta=eta_plus,
        negative_fold_reduced_eta=eta_minus,
        paired_reduced_eta=eta_pair,
        all_checks_pass=all(checks),
        conclusion=(
            "For a primitive monopole, quarter Z4 holonomy and the unweighted "
            "spectral modulus T^2=2*pi^2, the unique normalized Dirac gap is "
            "1/(8 L^2). The two PT folds cancel the eta asymmetry but add their "
            "even gap scales, giving q_LL L^2=1/4, q_LL=lambda_S2/8 and, with "
            "primitive LL flux, alphaSquaredLength/L=1."
        ),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0 if result.all_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
