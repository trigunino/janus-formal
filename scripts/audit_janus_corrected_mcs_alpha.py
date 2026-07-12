from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class CorrectedMCSAlphaAudit:
    target_alpha_squared_length_m: float
    chern_simons_level: int
    charge_amplitude: float
    rg_invariant_mass_inverse_m: float
    rg_invariant_energy_eV: float
    pi_exp_one_third: float
    corrected_exponent_sum: float
    old_exact_cancellation_residual: float
    planck_to_rg_mass_hierarchy: float
    planck_to_rg_log_hierarchy: float
    conclusion: str


def build_audit(
    target_alpha_squared_length_m: float = 1.0e26,
    chern_simons_level: int = 1,
    planck_length_m: float = 1.616255e-35,
) -> CorrectedMCSAlphaAudit:
    if target_alpha_squared_length_m <= 0.0:
        raise ValueError("target length must be positive")
    if chern_simons_level <= 0:
        raise ValueError("Chern-Simons level must be positive")
    if planck_length_m <= 0.0:
        raise ValueError("Planck length must be positive")

    level = float(chern_simons_level)
    constant = math.pi * math.exp(1.0 / 3.0)

    # From 2*pi*a_q = K.
    charge_amplitude = level / (2.0 * math.pi)

    # From K*Lambda_RG*A = pi*exp(1/3).
    rg_mass_inverse_m = constant / (level * target_alpha_squared_length_m)

    # hbar*c in eV*m.
    hbar_c_eV_m = 1.973269804e-7
    rg_energy_eV = hbar_c_eV_m * rg_mass_inverse_m

    # Correct matching: K*exp(x_*+X)=2*pi.
    corrected_sum = math.log(2.0 * math.pi / level)

    # The legacy x_*+X=0 ansatz would leave K instead of 2*pi.
    old_residual = level - 2.0 * math.pi

    planck_mass_inverse_m = 1.0 / planck_length_m
    hierarchy = planck_mass_inverse_m / rg_mass_inverse_m
    log_hierarchy = math.log(hierarchy)

    return CorrectedMCSAlphaAudit(
        target_alpha_squared_length_m=target_alpha_squared_length_m,
        chern_simons_level=chern_simons_level,
        charge_amplitude=charge_amplitude,
        rg_invariant_mass_inverse_m=rg_mass_inverse_m,
        rg_invariant_energy_eV=rg_energy_eV,
        pi_exp_one_third=constant,
        corrected_exponent_sum=corrected_sum,
        old_exact_cancellation_residual=old_residual,
        planck_to_rg_mass_hierarchy=hierarchy,
        planck_to_rg_log_hierarchy=log_hierarchy,
        conclusion=(
            "The standard Maxwell-Chern-Simons normalization replaces the "
            "arbitrary unit amplitude by a_q=K/(2*pi), shifts the exponent "
            "matching to K*exp(x_*+X)=2*pi, and makes the required RG-invariant "
            "mass explicit.  The remaining prediction problem is to compute "
            "that invariant mass and the realized integer level from the "
            "microscopic theory."
        ),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
