from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class WorldvolumeQuantumAudit:
    target_alpha_squared_length_m: float
    planck_length_m: float
    hierarchy_ratio: float
    hierarchy_exponent: float
    required_beta0_g_squared: float
    coupling_for_beta0_1: float
    coupling_for_beta0_7: float
    coupling_for_beta0_11: float
    log_sensitivity_to_coupling: float
    required_ll_charge_inverse_m2: float
    required_ll_tension_inverse_m: float
    required_lock_constant_for_k1_beta7: float
    required_lock_constant_for_k1_beta11: float
    flat_direction_predictive: bool
    conclusion: str


def build_audit(
    target_alpha_squared_length_m: float = 1.0e26,
    planck_length_m: float = 1.616255e-35,
) -> WorldvolumeQuantumAudit:
    if target_alpha_squared_length_m <= 0.0 or planck_length_m <= 0.0:
        raise ValueError("all lengths must be positive")

    ratio = target_alpha_squared_length_m / planck_length_m
    exponent = math.log(2.0 * ratio)
    beta_g2 = 8.0 * math.pi**2 / exponent

    def coupling(beta0: float) -> float:
        return math.sqrt(beta_g2 / beta0)

    # log R = log(l_P/2) + 8*pi^2/(beta0*g^2)
    # d log R / d log g = -16*pi^2/(beta0*g^2) = -2 X.
    sensitivity = -2.0 * exponent

    q_ll = 1.0 / (4.0 * target_alpha_squared_length_m**2)
    chi = 1.0 / (8.0 * math.pi * target_alpha_squared_length_m)

    # If a microscopic lock gives beta0*g^2 = beta0*c/k, then for k=1
    # the required c is simply (beta0*g^2)/beta0.
    c_beta7 = beta_g2 / 7.0
    c_beta11 = beta_g2 / 11.0

    return WorldvolumeQuantumAudit(
        target_alpha_squared_length_m=target_alpha_squared_length_m,
        planck_length_m=planck_length_m,
        hierarchy_ratio=ratio,
        hierarchy_exponent=exponent,
        required_beta0_g_squared=beta_g2,
        coupling_for_beta0_1=coupling(1.0),
        coupling_for_beta0_7=coupling(7.0),
        coupling_for_beta0_11=coupling(11.0),
        log_sensitivity_to_coupling=sensitivity,
        required_ll_charge_inverse_m2=q_ll,
        required_ll_tension_inverse_m=chi,
        required_lock_constant_for_k1_beta7=c_beta7,
        required_lock_constant_for_k1_beta11=c_beta11,
        flat_direction_predictive=False,
        conclusion=(
            "Dimensional transmutation can generate the required hierarchy from "
            "a moderate UV coupling, but the prediction is exponentially "
            "sensitive. A unique no-fit radius requires the microscopic theory "
            "to fix beta0*g_UV^2, the vacuum, and the LL charge normalization."
        ),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
