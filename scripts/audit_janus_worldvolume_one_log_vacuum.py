from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class OneLogVacuumAudit:
    potential: str
    first_derivative: str
    stationary_log_ratio: str
    stationary_condensate: str
    vacuum_energy: str
    radial_curvature: str
    derivative_factorization_residual: str
    stable_for_positive_log_coefficient: bool
    all_symbolic_checks_pass: bool


def build_audit() -> OneLogVacuumAudit:
    v, mu, lam, b = sp.symbols("v mu lam b", positive=True)
    x = sp.symbols("x", real=True)

    potential = v**6 * (lam + b * sp.log(v / mu))
    first = sp.factor(sp.diff(potential, v))
    stationary_x = sp.simplify(-(6 * lam + b) / (6 * b))
    stationary_v = sp.simplify(mu * sp.exp(stationary_x))
    energy = sp.simplify(potential.subs(v, stationary_v))
    curvature = sp.simplify(sp.diff(potential, v, 2).subs(v, stationary_v))

    log_potential = mu**6 * sp.exp(6 * x) * (lam + b * x)
    log_derivative = sp.diff(log_potential, x)
    factorized = 6 * b * mu**6 * sp.exp(6 * x) * (x - stationary_x)
    factorization_residual = sp.simplify(log_derivative - factorized)

    checks = [
        sp.simplify(first - v**5 * (6 * lam + b + 6 * b * sp.log(v / mu))) == 0,
        sp.simplify(energy + b * stationary_v**6 / 6) == 0,
        sp.simplify(curvature - 6 * b * stationary_v**4) == 0,
        factorization_residual == 0,
    ]

    return OneLogVacuumAudit(
        potential=str(potential),
        first_derivative=str(first),
        stationary_log_ratio=str(stationary_x),
        stationary_condensate=str(stationary_v),
        vacuum_energy=str(energy),
        radial_curvature=str(curvature),
        derivative_factorization_residual=str(factorization_residual),
        stable_for_positive_log_coefficient=True,
        all_symbolic_checks_pass=all(checks),
    )


def main() -> int:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    return 0 if audit.all_symbolic_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
