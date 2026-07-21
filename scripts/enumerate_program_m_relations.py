"""MF-ENUM-001: enumerate finite binary relations up to object relabelling."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path


def relabel(mask: int, n: int, permutation: tuple[int, ...]) -> int:
    """Transport a relation along the old-index -> new-index permutation."""
    result = 0
    for source in range(n):
        for target in range(n):
            if mask & (1 << (source * n + target)):
                result |= 1 << (permutation[source] * n + permutation[target])
    return result


def canonical_mask(mask: int, n: int) -> int:
    """Canonical representative of a relation under all vertex relabellings."""
    return min(relabel(mask, n, p) for p in itertools.permutations(range(n)))


def reflexive_transitive_closure(mask: int, n: int) -> int:
    rows = [0] * n
    for source in range(n):
        rows[source] = 1 << source
        for target in range(n):
            if mask & (1 << (source * n + target)):
                rows[source] |= 1 << target
    for middle in range(n):
        middle_bit = 1 << middle
        for source in range(n):
            if rows[source] & middle_bit:
                rows[source] |= rows[middle]
    return sum(
        1 << (source * n + target)
        for source, row in enumerate(rows)
        for target in range(n)
        if row & (1 << target)
    )


def strongly_connected_components(closure: int, n: int) -> tuple[tuple[int, ...], ...]:
    unseen = set(range(n))
    components: list[tuple[int, ...]] = []
    while unseen:
        root = min(unseen)
        component = tuple(
            vertex
            for vertex in sorted(unseen)
            if closure & (1 << (root * n + vertex))
            and closure & (1 << (vertex * n + root))
        )
        components.append(component)
        unseen.difference_update(component)
    return tuple(components)


def _permute_square_mask(mask: int, size: int, permutation: tuple[int, ...]) -> int:
    result = 0
    for source in range(size):
        for target in range(size):
            if mask & (1 << (source * size + target)):
                result |= 1 << (permutation[source] * size + permutation[target])
    return result


def compressed_signature(mask: int, n: int, level: str) -> tuple[object, ...]:
    """Canonical lossy signature of the decorated reachability skeleton."""
    closure = reflexive_transitive_closure(mask, n)
    components = strongly_connected_components(closure, n)
    component_of = {
        vertex: index for index, component in enumerate(components) for vertex in component
    }
    size = len(components)
    quotient = 0
    bridge_counts = [0] * (size * size)
    internal_counts = [0] * size
    for source in range(n):
        for target in range(n):
            source_component = component_of[source]
            target_component = component_of[target]
            if closure & (1 << (source * n + target)):
                quotient |= 1 << (source_component * size + target_component)
            if mask & (1 << (source * n + target)):
                if source_component == target_component:
                    internal_counts[source_component] += 1
                else:
                    bridge_counts[source_component * size + target_component] += 1

    signatures = []
    for permutation in itertools.permutations(range(size)):
        quotient_permuted = _permute_square_mask(quotient, size, permutation)
        sizes_permuted = [0] * size
        internal_permuted = [0] * size
        bridges_permuted = [0] * (size * size)
        for old in range(size):
            sizes_permuted[permutation[old]] = len(components[old])
            internal_permuted[permutation[old]] = internal_counts[old]
        for old_source in range(size):
            for old_target in range(size):
                new_source = permutation[old_source]
                new_target = permutation[old_target]
                bridges_permuted[new_source * size + new_target] = bridge_counts[
                    old_source * size + old_target
                ]
        if level == "bare_skeleton":
            payload = (size, quotient_permuted)
        elif level == "fiber_sizes":
            payload = (size, tuple(sizes_permuted), quotient_permuted)
        elif level == "bridge_existence":
            payload = (
                size,
                tuple(sizes_permuted),
                quotient_permuted,
                tuple(int(count > 0) for count in bridges_permuted),
            )
        elif level == "edge_counts":
            payload = (
                size,
                tuple(sizes_permuted),
                quotient_permuted,
                tuple(internal_permuted),
                tuple(bridges_permuted),
            )
        else:
            raise ValueError(f"unknown compression level: {level}")
        signatures.append(payload)
    return min(signatures)


def compression_audit(n: int) -> dict[str, object]:
    canonical = sorted({canonical_mask(mask, n) for mask in range(1 << (n * n))})
    levels = ("bare_skeleton", "fiber_sizes", "bridge_existence", "edge_counts")
    result: dict[str, object] = {}
    for level in levels:
        groups: dict[tuple[object, ...], list[int]] = {}
        for mask in canonical:
            groups.setdefault(compressed_signature(mask, n, level), []).append(mask)
        collision = next((masks[:2] for masks in groups.values() if len(masks) > 1), None)
        result[level] = {
            "signatures": len(groups),
            "colliding_relation_classes": sum(len(group) for group in groups.values() if len(group) > 1),
            "first_collision_masks": collision,
        }
    return result


def order_invariants(order_mask: int, size: int) -> dict[str, object]:
    """Exact invariants of a finite partial order; no dimension interpretation."""
    strict_relations = sum(
        1
        for source in range(size)
        for target in range(size)
        if source != target and order_mask & (1 << (source * size + target))
    )
    height = 0
    width = 0
    for subset in range(1 << size):
        vertices = [vertex for vertex in range(size) if subset & (1 << vertex)]
        is_chain = all(
            order_mask & (1 << (a * size + b))
            or order_mask & (1 << (b * size + a))
            for index, a in enumerate(vertices)
            for b in vertices[index + 1 :]
        )
        is_antichain = all(
            not order_mask & (1 << (a * size + b))
            and not order_mask & (1 << (b * size + a))
            for index, a in enumerate(vertices)
            for b in vertices[index + 1 :]
        )
        if is_chain:
            height = max(height, len(vertices))
        if is_antichain:
            width = max(width, len(vertices))
    interval_sizes = []
    for lower in range(size):
        for upper in range(size):
            if not order_mask & (1 << (lower * size + upper)):
                continue
            interval_sizes.append(
                sum(
                    bool(order_mask & (1 << (lower * size + middle)))
                    and bool(order_mask & (1 << (middle * size + upper)))
                    for middle in range(size)
                )
            )
    denominator = size * (size - 1)
    return {
        "elements": size,
        "strict_relations": strict_relations,
        "ordering_fraction": [2 * strict_relations, denominator] if denominator else [0, 0],
        "height": height,
        "width": width,
        "closed_interval_size_profile": sorted(interval_sizes),
    }


def dimension_invariant_audit(n: int) -> dict[str, object]:
    canonical = {canonical_mask(mask, n) for mask in range(1 << (n * n))}
    skeletons = {
        compressed_signature(mask, n, "bare_skeleton") for mask in canonical
    }
    groups: dict[tuple[int, int], list[tuple[int, int]]] = {}
    full_groups: dict[tuple[object, ...], list[tuple[int, int]]] = {}
    for size, order_mask in sorted(skeletons):
        invariants = order_invariants(order_mask, size)
        fraction_key = (size, int(invariants["strict_relations"]))
        full_key = (
            size,
            int(invariants["strict_relations"]),
            int(invariants["height"]),
            int(invariants["width"]),
            tuple(invariants["closed_interval_size_profile"]),
        )
        groups.setdefault(fraction_key, []).append((size, order_mask))
        full_groups.setdefault(full_key, []).append((size, order_mask))
    fraction_collision = next((group[:2] for group in groups.values() if len(group) > 1), None)
    full_collision = next((group[:2] for group in full_groups.values() if len(group) > 1), None)
    return {
        "skeleton_orders": len(skeletons),
        "ordering_fraction_signatures": len(groups),
        "ordering_fraction_first_collision": fraction_collision,
        "height_width_interval_signatures": len(full_groups),
        "height_width_interval_first_collision": full_collision,
    }


def linear_extensions(order_mask: int, size: int) -> tuple[tuple[int, ...], ...]:
    """All linear extensions of a finite partial order."""
    extensions = []
    for permutation in itertools.permutations(range(size)):
        rank = {vertex: index for index, vertex in enumerate(permutation)}
        if all(
            source == target
            or not order_mask & (1 << (source * size + target))
            or rank[source] < rank[target]
            for source in range(size)
            for target in range(size)
        ):
            extensions.append(permutation)
    return tuple(extensions)


def product_order_embedding(
    order_mask: int, size: int
) -> tuple[tuple[int, int], ...] | None:
    """Find exact rank coordinates in two product-ordered chains, if possible."""
    extensions = linear_extensions(order_mask, size)
    for first in extensions:
        first_rank = {vertex: index for index, vertex in enumerate(first)}
        for second in extensions:
            second_rank = {vertex: index for index, vertex in enumerate(second)}
            induced = 0
            for source in range(size):
                for target in range(size):
                    if (
                        first_rank[source] <= first_rank[target]
                        and second_rank[source] <= second_rank[target]
                    ):
                        induced |= 1 << (source * size + target)
            if induced == order_mask:
                return tuple(
                    (first_rank[vertex], second_rank[vertex])
                    for vertex in range(size)
                )
    return None


def standard_example_order(dimension: int) -> int:
    """The standard example S_d: a_i < b_j exactly when i != j."""
    size = 2 * dimension
    mask = sum(1 << (vertex * size + vertex) for vertex in range(size))
    for i in range(dimension):
        for j in range(dimension):
            if i != j:
                mask |= 1 << (i * size + dimension + j)
    return mask


def minkowski_two_order_audit() -> dict[str, object]:
    """Positive and negative exact order tests for the 1+1 target."""
    chain_size = 3
    chain = sum(
        1 << (source * chain_size + target)
        for source in range(chain_size)
        for target in range(chain_size)
        if source <= target
    )
    s3_size = 6
    s3 = standard_example_order(3)
    residuals = []
    for lower in range(chain_size):
        for upper in range(lower, chain_size):
            delta = upper - lower
            count = delta + 1
            volume = Fraction(delta * delta, 2)
            count_error = abs(Fraction(count) - 2 * volume)
            residuals.append(
                {
                    "interval": [lower, upper],
                    "count": count,
                    "volume": [volume.numerator, volume.denominator],
                    "count_volume_abs_error": [
                        count_error.numerator,
                        count_error.denominator,
                    ],
                    "chain_time_abs_error": [0, 1],
                }
            )
    return {
        "scope": "order compatibility only; volume and chain-time laws not tested",
        "positive": {
            "name": "three-element chain",
            "size": chain_size,
            "order_mask": chain,
            "null_rank_coordinates": product_order_embedding(chain, chain_size),
            "finite_gate": {
                "density": [2, 1],
                "count_tolerance": [1, 1],
                "chain_to_time": [1, 1],
                "time_tolerance": [0, 1],
                "all_endpoint_diamonds": residuals,
            },
        },
        "negative": {
            "name": "standard example S_3",
            "size": s3_size,
            "order_mask": s3,
            "null_rank_coordinates": product_order_embedding(s3, s3_size),
        },
    }


def minkowski_two_scaling_audit(
    sizes: tuple[int, ...] = (4, 8, 16, 32, 64),
) -> dict[str, object]:
    """Exact full-diamond scaling plus a persistent directional time test."""
    rows = []
    for size in sizes:
        if size < 3:
            raise ValueError("scaling sizes must be at least 3")
        expected = (size - 1) ** 2  # density 2 times volume (size-1)^2 / 2
        grid_error = Fraction(size * size - expected, expected)
        diagonal_error = Fraction(abs(size - expected), expected)
        aspect_unit = (size - 1) // 2
        chain_clock = Fraction(3 * aspect_unit, 2)
        proper_time = math.sqrt(2) * aspect_unit
        anisotropy = abs(float(chain_clock) - proper_time) / proper_time
        rows.append(
            {
                "linear_size": size,
                "density": [2, 1],
                "diagonal_chain_full_volume_relative_error": [
                    diagonal_error.numerator,
                    diagonal_error.denominator,
                ],
                "square_grid_full_volume_relative_error": [
                    grid_error.numerator,
                    grid_error.denominator,
                ],
                "square_grid_diagonal_chain_time_relative_error": 0.0,
                "square_grid_two_to_one_chain_time_relative_error": anisotropy,
            }
        )
    return {
        "scope": "deterministic lattices; no Poisson or Lorentz-invariance claim",
        "conventions": {
            "density": 2,
            "diagonal_chain_to_time": 1,
            "square_grid_chain_to_time": [1, 2],
            "directional_probe": "null-coordinate extents 2:1",
        },
        "rows": rows,
    }


def open_sets(closure: int, n: int, *, upper: bool) -> tuple[int, ...]:
    result = []
    for subset in range(1 << n):
        valid = True
        for source in range(n):
            for target in range(n):
                reaches = bool(closure & (1 << (source * n + target)))
                if not reaches:
                    continue
                if upper and subset & (1 << source) and not subset & (1 << target):
                    valid = False
                if not upper and subset & (1 << target) and not subset & (1 << source):
                    valid = False
        if valid:
            result.append(subset)
    return tuple(result)


def enumerate_size(n: int) -> dict[str, object]:
    canonical = {canonical_mask(mask, n) for mask in range(1 << (n * n))}
    scc_distribution: Counter[int] = Counter()
    closure_classes: set[int] = set()
    orientation_independent = 0
    for mask in canonical:
        closure = reflexive_transitive_closure(mask, n)
        closure_classes.add(canonical_mask(closure, n))
        scc_distribution[len(strongly_connected_components(closure, n))] += 1
        if open_sets(closure, n, upper=True) == open_sets(closure, n, upper=False):
            orientation_independent += 1
    return {
        "objects": n,
        "labelled_relations": 1 << (n * n),
        "isomorphism_classes": len(canonical),
        "reachability_classes": len(closure_classes),
        "orientation_independent_classes": orientation_independent,
        "classes_by_scc_count": dict(sorted(scc_distribution.items())),
    }


def run(max_objects: int = 4) -> dict[str, object]:
    if not 1 <= max_objects <= 4:
        raise ValueError("the audited range is 1..4 objects")
    return {
        "program": "MF-ENUM-001",
        "conventions": {
            "loops": "allowed",
            "relation": "directed binary relation",
            "equivalence": "simultaneous object relabelling",
            "reachability": "reflexive-transitive closure",
        },
        "results": [enumerate_size(n) for n in range(1, max_objects + 1)],
        "compression": {str(n): compression_audit(n) for n in range(1, max_objects + 1)},
        "dimension_invariants": {
            str(n): dimension_invariant_audit(n) for n in range(1, max_objects + 1)
        },
        "minkowski_two_order_audit": minkowski_two_order_audit(),
        "minkowski_two_scaling_audit": minkowski_two_scaling_audit(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-objects", type=int, default=4)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(run(args.max_objects), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
