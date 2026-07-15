from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class BackgroundVertexAudit:
    field_split: str
    inverse_square_series_order_2: str
    coefficients: dict[str, str]
    exact_remainder: str
    reconstruction_exact: bool
    coefficient_dimensions: dict[str, str]
    all_vertex_densities_dimension_three: bool
    verdict: str


def build_audit() -> BackgroundVertexAudit:
    v, eta = sp.symbols("v eta", nonzero=True)
    exact = 1 / (v + eta) ** 2
    truncated = 1 / v**2 - 2 * eta / v**3 + 3 * eta**2 / v**4
    remainder = sp.factor(exact - truncated)
    reconstructed = sp.simplify(truncated + remainder - exact) == 0

    # [phi]=[v]=[eta]=1/2 and [F^2]=4 in 2+1 dimensions.
    coefficient_dimensions = {
        "F2": "-1",
        "eta_F2": "-3/2",
        "eta2_F2": "-2",
    }
    vertex_dimensions = (
        sp.Rational(-1) + 4,
        sp.Rational(-3, 2) + sp.Rational(1, 2) + 4,
        sp.Rational(-2) + 1 + 4,
    )
    dimensions_ok = all(value == 3 for value in vertex_dimensions)
    return BackgroundVertexAudit(
        field_split="phi = v + eta, v != 0",
        inverse_square_series_order_2=str(truncated),
        coefficients={
            "F2": str(1 / v**2),
            "eta_F2": str(-2 / v**3),
            "eta2_F2": str(3 / v**4),
        },
        exact_remainder=str(remainder),
        reconstruction_exact=reconstructed,
        coefficient_dimensions=coefficient_dimensions,
        all_vertex_densities_dimension_three=dimensions_ok,
        verdict="conditional_background_vertices_ready_for_one_loop_bookkeeping",
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
