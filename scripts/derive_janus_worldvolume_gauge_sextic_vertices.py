from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class GaugeSexticVertexAudit:
    expansion_order: int
    coefficients: dict[str, str]
    coefficient_formula_verified: bool
    linear_quadratic_ring_partitions: tuple[tuple[int, int], ...]
    direct_eta6_vertex_present: bool
    sufficient_for_one_loop_six_point_bookkeeping: bool
    verdict: str


def build_audit(expansion_order: int = 6) -> GaugeSexticVertexAudit:
    if expansion_order < 0:
        raise ValueError("expansion_order must be nonnegative")
    v, eta = sp.symbols("v eta", nonzero=True)
    series = sp.series((v + eta) ** -2, eta, 0, expansion_order + 1).removeO()
    coefficients = {
        f"eta{n}_F2": str(sp.expand(series).coeff(eta, n))
        for n in range(expansion_order + 1)
    }
    formula_ok = all(
        sp.simplify(
            sp.expand(series).coeff(eta, n) - ((-1) ** n * (n + 1) / v ** (n + 2))
        )
        == 0
        for n in range(expansion_order + 1)
    )
    partitions = tuple((linear, quadratic) for quadratic in range(4) for linear in [6 - 2 * quadratic])
    direct = expansion_order >= 6 and coefficients.get("eta6_F2") == "7/v**8"
    sufficient = formula_ok and direct
    return GaugeSexticVertexAudit(
        expansion_order=expansion_order,
        coefficients=coefficients,
        coefficient_formula_verified=formula_ok,
        linear_quadratic_ring_partitions=partitions,
        direct_eta6_vertex_present=direct,
        sufficient_for_one_loop_six_point_bookkeeping=sufficient,
        verdict=("gauge_sextic_vertex_basis_ready" if sufficient else "increase_expansion_to_order_six"),
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
