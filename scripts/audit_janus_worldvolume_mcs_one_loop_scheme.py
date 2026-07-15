from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class MCSOneLoopSchemeAudit:
    cutoff_derivative: str
    large_cutoff_derivative: str
    divergent_potential_term: str
    finite_potential_term: str
    induced_scalar_shapes: dict[str, str]
    quartic_counterterm_required_in_cutoff_scheme: bool
    logarithmic_divergence_found_at_this_order: bool
    mcs_one_loop_ms_sextic_beta_contribution: int
    sextic_finite_part_scheme_independent: bool
    verdict: str


def build_audit() -> MCSOneLoopSchemeAudit:
    cutoff, mass = sp.symbols("Lambda m", positive=True)
    # d/dm [1/2 integral d^3p/(2pi)^3 log(p^2+m^2)] with a sharp radial cutoff.
    derivative = mass / (2 * sp.pi**2) * (
        cutoff - mass * sp.atan(cutoff / mass)
    )
    large_cutoff = cutoff * mass / (2 * sp.pi**2) - mass**2 / (4 * sp.pi)
    divergent = cutoff * mass**2 / (4 * sp.pi**2)
    finite = -mass**3 / (12 * sp.pi)
    # For the candidate normalization, m_CS is proportional to |kappa| phi^2.
    shapes = {
        "Lambda_m2": "Lambda*kappa^2*phi^4",
        "m3": "abs(kappa)^3*phi^6",
    }
    return MCSOneLoopSchemeAudit(
        cutoff_derivative=str(derivative),
        large_cutoff_derivative=str(large_cutoff),
        divergent_potential_term=str(divergent),
        finite_potential_term=str(finite),
        induced_scalar_shapes=shapes,
        quartic_counterterm_required_in_cutoff_scheme=True,
        logarithmic_divergence_found_at_this_order=False,
        mcs_one_loop_ms_sextic_beta_contribution=0,
        sextic_finite_part_scheme_independent=False,
        verdict="power_subtractions_and_finite_sextic_condition_required",
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
