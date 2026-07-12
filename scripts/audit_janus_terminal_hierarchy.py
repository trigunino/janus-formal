from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class HierarchyAudit:
    target_radius_m: float
    planck_length_m: float
    radius_to_planck_ratio: float
    primitive_planck_radius_m: float
    required_ll_charge_inverse_m2: float
    required_ll_tension_inverse_m: float
    required_flux_integer_if_planck_charge: float
    required_casimir_coefficient: float
    transmutation_exponent: float
    required_beta0_times_g_squared: float
    g_for_beta0_7: float
    g_for_beta0_11: float
    hierarchy_classification: str


def build_audit(
    target_radius_m: float = 1.0e26,
    planck_length_m: float = 1.616255e-35,
) -> HierarchyAudit:
    if target_radius_m <= 0.0 or planck_length_m <= 0.0:
        raise ValueError("lengths must be positive")

    ratio = target_radius_m / planck_length_m

    # Primitive LL law: 16 q^2 R^4 = 1.
    q_required = 1.0 / (4.0 * target_radius_m**2)
    chi_required = 1.0 / (8.0 * math.pi * target_radius_m)

    # General flux law: 16 q^2 R^4 = n^2.  For q=1/l_P^2,
    # |n| = 4 R^2/l_P^2 = (2R/l_P)^2.
    flux_integer = (2.0 * ratio) ** 2

    # Casimir closure from 3 L^2 = 8 pi C l_P^2.
    casimir_coefficient = 3.0 * ratio**2 / (8.0 * math.pi)

    # Generic asymptotically-free transmutation exit:
    # ell_eff = ell_P exp(X), X = 8 pi^2/(beta0 g^2), and R=ell_eff/2.
    exponent = math.log(2.0 * ratio)
    beta0_g2 = 8.0 * math.pi**2 / exponent
    g7 = math.sqrt(beta0_g2 / 7.0)
    g11 = math.sqrt(beta0_g2 / 11.0)

    return HierarchyAudit(
        target_radius_m=target_radius_m,
        planck_length_m=planck_length_m,
        radius_to_planck_ratio=ratio,
        primitive_planck_radius_m=planck_length_m / 2.0,
        required_ll_charge_inverse_m2=q_required,
        required_ll_tension_inverse_m=chi_required,
        required_flux_integer_if_planck_charge=flux_integer,
        required_casimir_coefficient=casimir_coefficient,
        transmutation_exponent=exponent,
        required_beta0_times_g_squared=beta0_g2,
        g_for_beta0_7=g7,
        g_for_beta0_11=g11,
        hierarchy_classification=(
            "primitive topology plus Planck normalization is excluded for a "
            "cosmological throat; viable non-circular exits are a derived tiny "
            "charge, a huge non-primitive integer/degeneracy, or exponential "
            "dimensional transmutation"
        ),
    )


def main() -> int:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
