from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class MCSPropagatorAudit:
    kinetic_matrix: str
    transverse_propagator: str
    inverse_verified: bool
    denominator: str
    topological_mass_squared: str
    gauge_ring_superficial_degree: int
    logarithmic_beta_extracted: bool
    verdict: str


def build_audit() -> MCSPropagatorAudit:
    a, kappa, p = sp.symbols("a kappa p", nonzero=True, real=True)
    # Momentum aligned with the third Euclidean axis. The first two components
    # are the physical transverse block; the longitudinal block is gauge-fixed separately.
    kinetic = sp.Matrix([[a * p**2, kappa * p], [-kappa * p, a * p**2]])
    denominator = a**2 * p**2 + kappa**2
    propagator = sp.Matrix(
        [
            [a / denominator, -kappa / (p * denominator)],
            [kappa / (p * denominator), a / denominator],
        ]
    )
    inverse_ok = sp.simplify(kinetic * propagator - sp.eye(2)) == sp.zeros(2)
    vertices, internal_edges, loops = sp.symbols("V I L", integer=True)
    degree = 3 * loops + 2 * vertices - 2 * internal_edges
    ring_degree = int(degree.subs({loops: 1, internal_edges: vertices}))
    return MCSPropagatorAudit(
        kinetic_matrix=str(kinetic),
        transverse_propagator=str(propagator),
        inverse_verified=inverse_ok,
        denominator=str(denominator),
        topological_mass_squared=str(kappa**2 / a**2),
        gauge_ring_superficial_degree=ring_degree,
        logarithmic_beta_extracted=False,
        verdict="propagator_ready_tensor_integrals_not_evaluated",
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
