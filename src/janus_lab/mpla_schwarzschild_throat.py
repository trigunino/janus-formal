"""MPLA Schwarzschild throat local model primitives."""

from __future__ import annotations

import math


def mpla_areal_radius(rho: float, rs: float = 1.0) -> float:
    if rs <= 0.0:
        raise ValueError("rs must be positive")
    return float(rs) * (1.0 + math.log(math.cosh(float(rho))))


def mpla_areal_radius_prime(rho: float, rs: float = 1.0) -> float:
    if rs <= 0.0:
        raise ValueError("rs must be positive")
    return float(rs) * math.tanh(float(rho))


def mpla_areal_radius_second(rho: float, rs: float = 1.0) -> float:
    if rs <= 0.0:
        raise ValueError("rs must be positive")
    c = math.cosh(float(rho))
    return float(rs) / (c * c)


def mpla_throat_certificate(rs: float = 1.0) -> dict:
    r0 = mpla_areal_radius(0.0, rs)
    rp0 = mpla_areal_radius_prime(0.0, rs)
    rpp0 = mpla_areal_radius_second(0.0, rs)
    return {
        "R_Sigma": r0,
        "R_prime_at_Sigma": rp0,
        "R_second_at_Sigma": rpp0,
        "minimal_throat": rp0 == 0.0 and rpp0 > 0.0,
        "Z2_rho_reflection_even_radius": True,
        "absolute_scale_fixed_by_model": False,
        "absolute_scale_symbol": "R_s",
    }
