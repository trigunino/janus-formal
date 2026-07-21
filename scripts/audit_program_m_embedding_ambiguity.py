"""MF-MAN-008: exhaustive non-uniqueness audit for null-rank embeddings."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

try:
    from scripts.enumerate_program_m_relations import (
        canonical_mask,
        linear_extensions,
        reflexive_transitive_closure,
        relabel,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from enumerate_program_m_relations import (
        canonical_mask,
        linear_extensions,
        reflexive_transitive_closure,
        relabel,
    )


Coordinates = tuple[tuple[int, int], ...]


def is_partial_order(mask: int, size: int) -> bool:
    diagonal = sum(1 << (i * size + i) for i in range(size))
    if mask & diagonal != diagonal or reflexive_transitive_closure(mask, size) != mask:
        return False
    return all(
        source == target
        or not (
            mask & (1 << (source * size + target))
            and mask & (1 << (target * size + source))
        )
        for source in range(size)
        for target in range(size)
    )


def product_order_realizers(mask: int, size: int) -> tuple[Coordinates, ...]:
    """All exact embeddings obtained from pairs of linear-extension ranks."""
    extensions = linear_extensions(mask, size)
    realizers: set[Coordinates] = set()
    for first in extensions:
        first_rank = {vertex: index for index, vertex in enumerate(first)}
        for second in extensions:
            second_rank = {vertex: index for index, vertex in enumerate(second)}
            induced = sum(
                1 << (source * size + target)
                for source in range(size)
                for target in range(size)
                if first_rank[source] <= first_rank[target]
                and second_rank[source] <= second_rank[target]
            )
            if induced == mask:
                realizers.add(
                    tuple(
                        (first_rank[vertex], second_rank[vertex])
                        for vertex in range(size)
                    )
                )
    return tuple(sorted(realizers))


def order_automorphisms(mask: int, size: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        permutation
        for permutation in itertools.permutations(range(size))
        if relabel(mask, size, permutation) == mask
    )


def interval_square_signature(
    coordinates: Coordinates, mask: int, size: int
) -> tuple[int, ...]:
    """Canonical pullback of ds^2=-du*dv under order automorphisms.

    Translation and null-coordinate exchange already leave this signature
    unchanged. Rank coordinates fix the otherwise external scale convention.
    """
    signatures = []
    for permutation in order_automorphisms(mask, size):
        inverse = [0] * size
        for old, new in enumerate(permutation):
            inverse[new] = old
        signatures.append(
            tuple(
                -(
                    coordinates[inverse[target]][0]
                    - coordinates[inverse[source]][0]
                )
                * (
                    coordinates[inverse[target]][1]
                    - coordinates[inverse[source]][1]
                )
                for source in range(size)
                for target in range(source + 1, size)
            )
        )
    return min(signatures)


def ambiguity_audit(max_size: int = 4) -> dict[str, object]:
    if max_size < 1 or max_size > 4:
        raise ValueError("the exhaustive audit is certified only for 1 <= max_size <= 4")
    rows = []
    first_witness = None
    for size in range(1, max_size + 1):
        canonical_relations = {
            canonical_mask(mask, size) for mask in range(1 << (size * size))
        }
        orders = sorted(mask for mask in canonical_relations if is_partial_order(mask, size))
        embeddable = 0
        ambiguous = 0
        for mask in orders:
            realizers = product_order_realizers(mask, size)
            if not realizers:
                continue
            embeddable += 1
            classes: dict[tuple[int, ...], Coordinates] = {}
            for coordinates in realizers:
                classes.setdefault(
                    interval_square_signature(coordinates, mask, size), coordinates
                )
            if len(classes) > 1:
                ambiguous += 1
                if first_witness is None:
                    first_witness = {
                        "size": size,
                        "order_mask": mask,
                        "strict_pairs": [
                            [source, target]
                            for source in range(size)
                            for target in range(size)
                            if source != target
                            and mask & (1 << (source * size + target))
                        ],
                        "realizer_count": len(realizers),
                        "metric_signature_count": len(classes),
                        "representatives": [
                            {
                                "null_rank_coordinates": coordinates,
                                "pairwise_ds2_signature": signature,
                            }
                            for signature, coordinates in sorted(classes.items())
                        ],
                    }
        rows.append(
            {
                "size": size,
                "partial_order_classes": len(orders),
                "product_order_embeddable_classes": embeddable,
                "metric_ambiguous_classes": ambiguous,
            }
        )
    return {
        "program": "MF-MAN-008",
        "scope": "exhaustive up to relabelling for at most four objects",
        "external_conventions": [
            "two linear-extension ranks are interpreted as null coordinates",
            "rank spacing fixes a coordinate scale",
            "the comparison uses ds^2=-du*dv",
        ],
        "rows": rows,
        "first_nonunique_witness": first_witness,
        "conclusion": (
            "exact order compatibility with Minkowski 1+1 does not select a unique "
            "rank geometry, even modulo order automorphisms"
        ),
        "claims_not_made": [
            "physical spacetime or causal interpretation",
            "continuum or macroscopic non-uniqueness",
            "failure of every possible reconstruction algorithm",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-size", type=int, default=4)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(ambiguity_audit(args.max_size), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
