from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class OneLoopAnomalousAudit:
    dimension: str
    tested_denominator_powers: tuple[int, ...]
    gamma_arguments_at_epsilon_zero: tuple[str, ...]
    pole_residues: tuple[str, ...]
    one_loop_ms_wavefunction_pole: str
    verdict: str


def build_audit(max_power: int = 6) -> OneLoopAnomalousAudit:
    epsilon = sp.symbols("epsilon")
    dimension = 3 - 2 * epsilon
    powers = tuple(range(1, max_power + 1))
    arguments = tuple(sp.simplify(power - sp.Rational(3, 2)) for power in powers)
    residues = tuple(
        sp.simplify(sp.limit(epsilon * sp.gamma(power - dimension / 2), epsilon, 0))
        for power in powers
    )
    assert all(residue == 0 for residue in residues)
    return OneLoopAnomalousAudit(
        dimension=str(dimension),
        tested_denominator_powers=powers,
        gamma_arguments_at_epsilon_zero=tuple(map(str, arguments)),
        pole_residues=tuple(map(str, residues)),
        one_loop_ms_wavefunction_pole="0",
        verdict="no_one_loop_ms_anomalous_dimension_for_integer_power_bubbles",
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
