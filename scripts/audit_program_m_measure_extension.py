"""MF-MEAS-001: distinguish relational invariance from uniform counting measure."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

try:
    from scripts.audit_program_m_weight_selection_nogo import automorphisms
except ModuleNotFoundError:
    from audit_program_m_weight_selection_nogo import automorphisms


def invariant_vertex_weights(
    weights: tuple[int, ...], permutations: tuple[tuple[int, ...], ...]
) -> bool:
    return all(
        all(weights[permutation[x]] == weights[x] for x in range(len(weights)))
        for permutation in permutations
    )


def run_audit() -> dict[str, object]:
    vertices = (0, 1, 2)
    edges = frozenset(((0, 1), (1, 2)))
    relational_symmetries = automorphisms(vertices, edges)
    all_permutations = tuple(itertools.permutations(vertices))
    candidates = tuple(itertools.product(range(1, 4), repeat=3))
    relationally_invariant = tuple(
        weights
        for weights in candidates
        if invariant_vertex_weights(weights, relational_symmetries)
    )
    fully_uniform = tuple(
        weights
        for weights in candidates
        if invariant_vertex_weights(weights, all_permutations)
    )
    normalized_relational = tuple(w for w in relationally_invariant if w[0] == 1)
    normalized_uniform = tuple(w for w in fully_uniform if w[0] == 1)
    return {
        "program": "MF-MEAS-001",
        "witness": {
            "primitive_edges": [list(edge) for edge in sorted(edges)],
            "relational_automorphisms": [list(p) for p in relational_symmetries],
        },
        "counts": {
            "positive_integer_measures": len(candidates),
            "relationally_invariant": len(relationally_invariant),
            "relationally_invariant_after_first_atom_normalization": len(normalized_relational),
            "fully_relabelling_invariant": len(fully_uniform),
            "fully_relabelling_invariant_after_normalization": len(normalized_uniform),
        },
        "fully_uniform_candidates": [list(w) for w in fully_uniform],
        "gates": {
            "relational_invariance_does_not_select_measure": len(relationally_invariant) == 27,
            "relative_mass_ambiguity_survives_normalization": len(normalized_relational) == 9,
            "full_object_uniformity_forces_counting_measure_up_to_scale": (
                fully_uniform == ((1, 1, 1), (2, 2, 2), (3, 3, 3))
            ),
            "normalization_then_selects_counting_measure": normalized_uniform == ((1, 1, 1),),
        },
        "conclusion": (
            "an additive measure is not selected by relational invariance; counting "
            "measure emerges only after adding full object-uniformity, up to scale"
        ),
        "scope": (
            "finite atomic measures; no probability law, continuum limit or geometric "
            "volume correspondence is inferred"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(run_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
