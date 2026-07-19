"""MF-MAN-012: dimensionless density/chain-scale consistency audit."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

try:
    from scripts.audit_program_m_chain_time_selection import chain_time_fit
    from scripts.audit_program_m_embedding_ambiguity import (
        interval_square_signature,
        product_order_realizers,
    )
    from scripts.audit_program_m_volume_selection import (
        canonical_partial_orders,
        interval_count_volume_fit,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_chain_time_selection import chain_time_fit
    from audit_program_m_embedding_ambiguity import (
        interval_square_signature,
        product_order_realizers,
    )
    from audit_program_m_volume_selection import (
        canonical_partial_orders,
        interval_count_volume_fit,
    )


def _fraction(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def scale_consistency_audit(max_size: int = 5) -> dict[str, object]:
    if max_size < 1 or max_size > 5:
        raise ValueError("the exhaustive audit is certified only for 1 <= max_size <= 5")
    rows = []
    first_witness = None
    for size in range(1, max_size + 1):
        orders = canonical_partial_orders(size)
        ambiguous = equal_within_class = exact_pass = unique_best = 0
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
            scores = []
            for signature, coordinates in sorted(metric_classes.items()):
                volume_fit = interval_count_volume_fit(mask, size, coordinates)
                time_fit = chain_time_fit(mask, size, coordinates)
                density = Fraction(*volume_fit["calibrated_density"])
                chain_scale_squared = Fraction(
                    *time_fit["calibrated_chain_to_time_squared"]
                )
                consistency = 2 * density * chain_scale_squared
                score = abs(consistency - 1)
                scores.append(score)
                candidates.append(
                    {
                        "null_rank_coordinates": coordinates,
                        "pairwise_ds2_signature": signature,
                        "density": _fraction(density),
                        "chain_to_time_squared": _fraction(chain_scale_squared),
                        "two_density_chain_scale_squared": _fraction(consistency),
                        "absolute_distance_from_asymptotic_identity": _fraction(score),
                    }
                )
            if len(set(scores)) == 1:
                equal_within_class += 1
            if any(score == 0 for score in scores):
                exact_pass += 1
            if scores.count(min(scores)) == 1:
                unique_best += 1
            if first_witness is None:
                first_witness = {
                    "size": size,
                    "order_mask": mask,
                    "candidates": candidates,
                }
        rows.append(
            {
                "size": size,
                "partial_order_classes": len(orders),
                "metric_ambiguous_classes": ambiguous,
                "same_consistency_within_class": equal_within_class,
                "classes_with_exact_asymptotic_identity": exact_pass,
                "uniquely_closest_classes": unique_best,
            }
        )
    return {
        "program": "MF-MAN-012",
        "scope": "exhaustive up to relabelling for at most five objects",
        "dimensionless_identity": "2 * density * chainToTime^2 = 1",
        "derivation": (
            "external Minkowski 1+1 conventions V=tau^2/2, E[L]~2*sqrt(rho*V)"
        ),
        "rows": rows,
        "first_ambiguous_witness": first_witness,
        "conclusion": (
            "the dimensionless relation removes unit weighting but neither selects "
            "nor exactly accepts any ambiguous rank geometry through size five"
        ),
        "claims_not_made": [
            "a valid zero-tolerance finite-size test of an asymptotic law",
            "statistical rejection of Minkowski 1+1",
            "emergent geometry or physical time",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-size", type=int, default=5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(
        scale_consistency_audit(args.max_size), indent=2, sort_keys=True
    ) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
