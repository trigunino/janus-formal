from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class AuditResult:
    dt_du: str
    da_dt: str
    d2a_dt2: str
    a2_d2a_dt2: str
    q: str
    friedmann_identity_residual: str
    corrected_ode_residual: str
    displayed_ode_residual: str
    source_bridge_map_residual: str
    casimir_planck_coefficient_for_1e26m: float
    all_symbolic_checks_pass: bool


def build_audit() -> AuditResult:
    """Differentiate the published parametric solution and audit its constants."""

    u = sp.symbols("u", real=True)
    A, c, pi_c, G, E, R, M = sp.symbols(
        "A c pi_c G E R M", real=True, nonzero=True
    )

    a = A * sp.cosh(u) ** 2
    t = A / c * (1 + sp.sinh(2 * u) / 2 + u)
    dt_du = sp.simplify(sp.diff(t, u))
    da_dt = sp.simplify(sp.diff(a, u) / dt_du)
    d2a_dt2 = sp.simplify(sp.diff(da_dt, u) / dt_du)
    a2_d2a_dt2 = sp.simplify(a**2 * d2a_dt2)
    H = sp.simplify(da_dt / a)
    q = sp.simplify(-a * d2a_dt2 / da_dt**2)
    friedmann_residual = sp.simplify(1 - 2 * q - c**2 / (a**2 * H**2))

    # D'Agostini--Petit 2018, Eq. (11): A = alpha^2 = -8*pi*G*E/(3*c^2).
    source_sub = {A: -8 * pi_c * G * E / (3 * c**2)}
    corrected_residual = sp.simplify(
        (a2_d2a_dt2 + 4 * pi_c * G * E / 3).subs(source_sub)
    )
    displayed_residual = sp.factor(
        sp.simplify((a2_d2a_dt2 + 8 * pi_c * G * E / 3).subs(source_sub))
    )

    # Conditional same-radius bridge map: A=R and R=2GM/c^2.
    bridge_E = -3 * c**2 * R / (8 * pi_c * G)
    bridge_M = c**2 * R / (2 * G)
    source_bridge_map_residual = sp.simplify(4 * pi_c * bridge_E + 3 * bridge_M)

    # Diagnostic only: C = 3/(8*pi) * (L/l_P)^2 for a 1/L Casimir source.
    planck_length_m = 1.616255e-35
    target_length_m = 1.0e26
    casimir_coefficient = 3.0 / (8.0 * math.pi) * (
        target_length_m / planck_length_m
    ) ** 2

    checks = [
        sp.simplify(a2_d2a_dt2 - A * c**2 / 2) == 0,
        sp.simplify(q + 1 / (2 * sp.sinh(u) ** 2)) == 0,
        friedmann_residual == 0,
        corrected_residual == 0,
        sp.simplify(displayed_residual - 4 * pi_c * G * E / 3) == 0,
        source_bridge_map_residual == 0,
    ]

    return AuditResult(
        dt_du=str(dt_du),
        da_dt=str(da_dt),
        d2a_dt2=str(d2a_dt2),
        a2_d2a_dt2=str(a2_d2a_dt2),
        q=str(q),
        friedmann_identity_residual=str(friedmann_residual),
        corrected_ode_residual=str(corrected_residual),
        displayed_ode_residual=str(displayed_residual),
        source_bridge_map_residual=str(source_bridge_map_residual),
        casimir_planck_coefficient_for_1e26m=casimir_coefficient,
        all_symbolic_checks_pass=all(checks),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0 if result.all_symbolic_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
