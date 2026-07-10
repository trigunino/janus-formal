from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class BridgeLLAudit:
    finite_sphere_combination: str
    horizon_radial_polynomial: str
    ll_field_invariant: str
    primitive_flux_radius_law: str
    charge_tension_relation: str
    target_radius_m: float
    required_q_inverse_m2: float
    required_chi_inverse_m: float
    bridge_mass_kg: float
    global_mass_constant_kg: float
    planck_q_gives_radius_m: float
    all_symbolic_checks_pass: bool


def build_audit(target_radius_m: float = 1.0e26) -> BridgeLLAudit:
    """Audit the complete conditional bridge/LL algebra without fitting a scale."""

    A, r, Rs, c2, G, pi_c, E, M = sp.symbols(
        "A r Rs c2 G pi_c E M", real=True, nonzero=True
    )
    q, chi, F2, a0, n = sp.symbols(
        "q chi F2 a0 n", real=True, nonzero=True
    )

    # Cleared equations:
    # 3 c^2 A = -8 pi G E,
    # 3 M = -4 pi E r^3,
    # c^2 R_s = 2 G M.
    source = 3 * c2 * A + 8 * pi_c * G * E
    signed_mass = 3 * M + 4 * pi_c * E * r**3
    schwarzschild = c2 * Rs - 2 * G * M
    finite_combination = sp.factor(
        3 * schwarzschild + 2 * G * signed_mass - r**3 * source
    )

    # With R_s = A r^3 and the areal/horizon law A r = R_s.
    horizon_polynomial = sp.factor(A * r - A * r**3)

    # Wrong-sign Maxwell LL sector: a0=F2/4 and junction a0=1/8.
    f2_solution = sp.solve(
        [sp.Eq(a0, F2 / 4), sp.Eq(a0, sp.Rational(1, 8))],
        [F2, a0],
        dict=True,
    )[0][F2]

    primitive_radius = sp.Eq(16 * q**2 * Rs**4, 1)
    tension = sp.Eq(8 * pi_c * chi * Rs, 1)
    q2_from_radius = sp.solve(primitive_radius, q**2)[0]
    rs_from_tension = sp.solve(tension, Rs)[0]
    q2_tension = sp.factor(q2_from_radius.subs(Rs, rs_from_tension))

    # Diagnostics only.  The radius below is not used as an input to any proof.
    c_si = 299_792_458.0
    g_si = 6.67430e-11
    planck_length_m = 1.616255e-35
    q_required = 1.0 / (4.0 * target_radius_m**2)
    chi_required = 1.0 / (8.0 * math.pi * target_radius_m)
    bridge_mass = c_si**2 * target_radius_m / (2.0 * g_si)
    global_mass = -3.0 * bridge_mass / (4.0 * math.pi)
    planck_q = 1.0 / planck_length_m**2
    radius_from_planck_q = 1.0 / (2.0 * math.sqrt(planck_q))

    checks = [
        sp.expand(finite_combination + 3 * c2 * (A * r**3 - Rs)) == 0,
        horizon_polynomial == -A * r * (r - 1) * (r + 1),
        f2_solution == sp.Rational(1, 2),
        sp.simplify(q2_tension - 256 * pi_c**4 * chi**4) == 0,
        q_required > 0,
        chi_required > 0,
    ]

    return BridgeLLAudit(
        finite_sphere_combination=str(finite_combination),
        horizon_radial_polynomial=str(horizon_polynomial),
        ll_field_invariant=str(f2_solution),
        primitive_flux_radius_law=str(primitive_radius),
        charge_tension_relation=f"q**2 = {q2_tension}",
        target_radius_m=target_radius_m,
        required_q_inverse_m2=q_required,
        required_chi_inverse_m=chi_required,
        bridge_mass_kg=bridge_mass,
        global_mass_constant_kg=global_mass,
        planck_q_gives_radius_m=radius_from_planck_q,
        all_symbolic_checks_pass=all(checks),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0 if result.all_symbolic_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
