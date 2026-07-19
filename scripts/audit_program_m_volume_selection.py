"""MF-MAN-009: can interval counts select among ambiguous rank embeddings?"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

try:
    from scripts.audit_program_m_embedding_ambiguity import (
        interval_square_signature,
        product_order_realizers,
    )
    from scripts.enumerate_program_m_relations import (
        canonical_mask,
        reflexive_transitive_closure,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_embedding_ambiguity import (
        interval_square_signature,
        product_order_realizers,
    )
    from enumerate_program_m_relations import canonical_mask, reflexive_transitive_closure


def canonical_partial_orders(size: int) -> tuple[int, ...]:
    """Every unlabeled poset, using all forward relations then closing."""
    pairs = [(i, j) for i in range(size) for j in range(i + 1, size)]
    diagonal = sum(1 << (i * size + i) for i in range(size))
    orders = set()
    for edge_bits in range(1 << len(pairs)):
        relation = diagonal
        for index, (source, target) in enumerate(pairs):
            if edge_bits & (1 << index):
                relation |= 1 << (source * size + target)
        orders.add(
            canonical_mask(reflexive_transitive_closure(relation, size), size)
        )
    return tuple(sorted(orders))


def _fraction(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def interval_count_volume_fit(
    mask: int, size: int, coordinates: tuple[tuple[int, int], ...]
) -> dict[str, object] | None:
    """Calibrate density on largest intervals, score only the remaining ones."""
    samples: list[tuple[int, int, Fraction, int]] = []
    for lower in range(size):
        for upper in range(size):
            if lower == upper or not mask & (1 << (lower * size + upper)):
                continue
            count = sum(
                bool(mask & (1 << (lower * size + middle)))
                and bool(mask & (1 << (middle * size + upper)))
                for middle in range(size)
            )
            delta_u = coordinates[upper][0] - coordinates[lower][0]
            delta_v = coordinates[upper][1] - coordinates[lower][1]
            samples.append((lower, upper, Fraction(delta_u * delta_v, 2), count))
    if not samples:
        return None
    maximum_count = max(count for _, _, _, count in samples)
    calibration = [sample for sample in samples if sample[3] == maximum_count]
    validation = [sample for sample in samples if sample[3] < maximum_count]
    denominator = sum(volume * volume for _, _, volume, _ in calibration)
    density = sum(
        volume * count for _, _, volume, count in calibration
    ) / denominator
    residual = sum(
        (Fraction(count) - density * volume) ** 2
        for _, _, volume, count in validation
    )
    return {
        "calibrated_density": _fraction(density),
        "validation_sum_squared_count_residual": (
            _fraction(residual) if validation else None
        ),
        "calibration_interval_count": len(calibration),
        "validation_interval_count": len(validation),
        "intervals": [
            {
                "endpoints": [lower, upper],
                "count": count,
                "target_volume": _fraction(volume),
            }
            for lower, upper, volume, count in samples
        ],
    }


def volume_selection_audit(max_size: int = 5) -> dict[str, object]:
    if max_size < 1 or max_size > 5:
        raise ValueError("the exhaustive audit is certified only for 1 <= max_size <= 5")
    rows = []
    first_selected = None
    first_unresolved = None
    for size in range(1, max_size + 1):
        orders = canonical_partial_orders(size)
        ambiguous = selected = unresolved = 0
        for mask in orders:
            metric_classes = {}
            for coordinates in product_order_realizers(mask, size):
                metric_classes.setdefault(
                    interval_square_signature(coordinates, mask, size), coordinates
                )
            if len(metric_classes) < 2:
                continue
            ambiguous += 1
            candidates = []
            for signature, coordinates in sorted(metric_classes.items()):
                fit = interval_count_volume_fit(mask, size, coordinates)
                candidates.append(
                    {
                        "null_rank_coordinates": coordinates,
                        "pairwise_ds2_signature": signature,
                        "volume_fit": fit,
                    }
                )
            residuals = [
                Fraction(
                    *candidate["volume_fit"]["validation_sum_squared_count_residual"]
                )
                for candidate in candidates
                if candidate["volume_fit"] is not None
                and candidate["volume_fit"]["validation_sum_squared_count_residual"]
                is not None
            ]
            unique_best = (
                len(residuals) == len(candidates)
                and residuals.count(min(residuals)) == 1
            )
            witness = {
                "size": size,
                "order_mask": mask,
                "strict_pairs": [
                    [source, target]
                    for source in range(size)
                    for target in range(size)
                    if source != target
                    and mask & (1 << (source * size + target))
                ],
                "metric_classes": len(metric_classes),
                "unique_least_squares_choice": unique_best,
                "candidates": candidates,
            }
            if unique_best:
                selected += 1
                if first_selected is None:
                    first_selected = witness
            else:
                unresolved += 1
                if first_unresolved is None:
                    first_unresolved = witness
        rows.append(
            {
                "size": size,
                "partial_order_classes": len(orders),
                "metric_ambiguous_classes": ambiguous,
                "uniquely_selected_by_volume_fit": selected,
                "unresolved_after_volume_fit": unresolved,
            }
        )
    return {
        "program": "MF-MAN-009",
        "scope": "exhaustive up to relabelling for at most five objects",
        "selection_rule": (
            "calibrate one density by exact least squares on the strict closed "
            "order intervals of maximal cardinality, then score only the others"
        ),
        "external_conventions": [
            "linear-extension ranks are null coordinates",
            "Minkowski 1+1 volume is du*dv/2",
            "closed interval cardinality represents volume",
            "order-defined calibration/validation split and least-squares loss",
        ],
        "rows": rows,
        "first_uniquely_selected_witness": first_selected,
        "first_unresolved_witness": first_unresolved,
        "conclusion": (
            "interval counts sometimes break rank-embedding ambiguity but do not "
            "supply a general uniqueness principle"
        ),
        "claims_not_made": [
            "emergent Minkowski geometry",
            "statistical validity of fitting density on the tested candidate",
            "continuum uniqueness or the causal-set Hauptvermutung",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-size", type=int, default=5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(volume_selection_audit(args.max_size), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
