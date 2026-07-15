from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class MixedTwoLoopResidueAudit:
    transverse_numerator: str
    sunset_remainder: str
    kappa4_residue: str
    kappa2_lambda6_residue: str
    lambda6_squared_residue: str
    coupling_pole_residue: str
    conditional_ms_beta_coefficient: str
    composite_source_pole_residue: str
    composite_anomalous_coefficient: str
    non_ll_callan_symanzik_coefficient: str
    verdict: str


def build_audit() -> MixedTwoLoopResidueAudit:
    x, y, s, gauge_mass_sq, scalar_mass_sq, lambda6 = sp.symbols(
        "x y s mA2 mEta2 lambda6"
    )
    dot = (s - x - y) / 2
    numerator = sp.expand(x * y + dot**2 - 2 * gauge_mass_sq * dot)

    # The coefficient of the logarithmic sunset master is the remainder after
    # cancelling factors of its three propagator denominators.
    remainder = sp.factor(
        numerator.subs(
            {x: -gauge_mass_sq, y: -gauge_mass_sq, s: -scalar_mass_sq}
        )
    )
    assert sp.simplify(remainder - scalar_mass_sq**2 / 4) == 0

    # For V=lambda6*phi^6/6, m_eta^2=V''=5*lambda6*v^4.  The cumulant and
    # two gauge Wick contractions give net prefactor -v^-2.  Cancelling the
    # divergence with delta(lambda6)*v^6/6 yields the positive pole below.
    coupling_pole = sp.Rational(75, 128) * lambda6**2 / sp.pi**2
    beta_coefficient = sp.simplify(4 * coupling_pole / lambda6**2)
    source_pole = sp.Rational(5, 64) * lambda6 / sp.pi**2
    composite_anomalous = sp.simplify(4 * source_pole / lambda6)
    non_ll_cs = sp.simplify(
        sp.Rational(475, 32) / sp.pi**2 - 3 * composite_anomalous
    )

    return MixedTwoLoopResidueAudit(
        transverse_numerator=str(numerator),
        sunset_remainder=str(remainder),
        kappa4_residue="0",
        kappa2_lambda6_residue="0",
        lambda6_squared_residue="mEta2**2/4",
        coupling_pole_residue=str(coupling_pole),
        conditional_ms_beta_coefficient=str(beta_coefficient),
        composite_source_pole_residue=str(source_pole),
        composite_anomalous_coefficient=str(composite_anomalous),
        non_ll_callan_symanzik_coefficient=str(non_ll_cs),
        verdict="conditional_on_candidate_euclidean_mcs_feynman_rules",
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
