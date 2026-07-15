from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class SexticTwoLoopLogAudit:
    loops: int
    internal_edges: int
    superficial_degree_d3: int
    coupling_dimension_near_d3: str
    ms_beta_relation: str
    master_integral_formula: str
    master_integral_pole_residue: str
    repository_combinatorial_weight: str
    standard_normalization_weight: str
    pure_scalar_beta_coefficient: str
    standard_beta_coefficient: str
    literature_normalization_crosscheck: bool
    logarithmic_topology_identified: bool
    pole_residue_computed: bool
    beta_coefficient_computed: bool
    missing_inputs: tuple[str, ...]
    verdict: str


def build_audit() -> SexticTwoLoopLogAudit:
    epsilon, d, p2 = sp.symbols("epsilon d p2", positive=True)
    scalar_dimension = (d - 2) / 2
    coupling_dimension = sp.expand(d - 6 * scalar_dimension)
    near_three = sp.simplify(coupling_dimension.subs(d, 3 - 2 * epsilon))
    loops, internal_edges = 2, 3
    degree = 3 * loops - 2 * internal_edges
    master = (
        p2 ** (d - 3)
        / (4 * sp.pi) ** d
        * sp.gamma(d / 2 - 1) ** 3
        * sp.gamma(3 - d)
        / sp.gamma(3 * d / 2 - 3)
    )
    continued_master = master.subs(d, 3 - 2 * epsilon)
    pole_residue = sp.simplify(sp.limit(epsilon * continued_master, epsilon, 0, dir="+"))
    labeled_partition = sp.binomial(6, 3)
    attachment_per_vertex = sp.factorial(6) / sp.factorial(3)
    internal_pairings = sp.factorial(3)
    repository_weight = sp.simplify(
        sp.Rational(1, 2)
        * sp.Rational(1, 6) ** 2
        * labeled_partition
        * attachment_per_vertex**2
        * internal_pairings
        / (sp.factorial(6) / 6)
    )
    standard_weight = sp.simplify(
        sp.Rational(1, 2)
        * sp.Rational(1, sp.factorial(6)) ** 2
        * labeled_partition
        * attachment_per_vertex**2
        * internal_pairings
    )
    pure_scalar_beta = sp.simplify(4 * repository_weight * pole_residue)
    standard_beta = sp.simplify(4 * standard_weight * pole_residue)
    missing = (
        "nonzero_momentum_or_ir_mass_prescription",
        "subdivergence_subtractions",
        "ll_measure_diagrams",
    )
    return SexticTwoLoopLogAudit(
        loops=loops,
        internal_edges=internal_edges,
        superficial_degree_d3=degree,
        coupling_dimension_near_d3=str(near_three),
        ms_beta_relation="beta_lambda6 = 4*A*lambda6^2 + higher orders",
        master_integral_formula=str(master),
        master_integral_pole_residue=str(pole_residue),
        repository_combinatorial_weight=str(repository_weight),
        standard_normalization_weight=str(standard_weight),
        pure_scalar_beta_coefficient=str(pure_scalar_beta),
        standard_beta_coefficient=str(standard_beta),
        literature_normalization_crosscheck=standard_beta == 5 / (48 * sp.pi**2),
        logarithmic_topology_identified=degree == 0,
        pole_residue_computed=pole_residue == 1 / (64 * sp.pi**2),
        beta_coefficient_computed=pure_scalar_beta == 25 / (2 * sp.pi**2),
        missing_inputs=missing,
        verdict="pure_scalar_beta_ready_gauge_and_ll_contributions_open",
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
