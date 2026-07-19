"""MF-MAN-010: chain-time selection and conflict with number-volume."""

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
    from scripts.audit_program_m_volume_selection import (
        canonical_partial_orders,
        interval_count_volume_fit,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
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


def intrinsic_chain_steps(mask: int, size: int, lower: int, upper: int) -> int:
    interval = [
        vertex
        for vertex in range(size)
        if mask & (1 << (lower * size + vertex))
        and mask & (1 << (vertex * size + upper))
    ]
    best = 1
    for subset_mask in range(1 << len(interval)):
        subset = [
            interval[index]
            for index in range(len(interval))
            if subset_mask & (1 << index)
        ]
        if lower not in subset or upper not in subset:
            continue
        if all(
            mask & (1 << (left * size + right))
            or mask & (1 << (right * size + left))
            for index, left in enumerate(subset)
            for right in subset[index + 1 :]
        ):
            best = max(best, len(subset) - 1)
    return best


def chain_time_fit(
    mask: int, size: int, coordinates: tuple[tuple[int, int], ...]
) -> dict[str, object] | None:
    """Calibrate squared chain-to-time scale, validate on shorter chains."""
    samples = []
    for lower in range(size):
        for upper in range(size):
            if lower == upper or not mask & (1 << (lower * size + upper)):
                continue
            steps = intrinsic_chain_steps(mask, size, lower, upper)
            target_time_squared = (
                (coordinates[upper][0] - coordinates[lower][0])
                * (coordinates[upper][1] - coordinates[lower][1])
            )
            samples.append((lower, upper, steps, target_time_squared))
    if not samples:
        return None
    maximum_steps = max(steps for _, _, steps, _ in samples)
    calibration = [sample for sample in samples if sample[2] == maximum_steps]
    validation = [sample for sample in samples if sample[2] < maximum_steps]
    scale_squared = Fraction(
        sum(steps * steps * target for _, _, steps, target in calibration),
        sum(steps**4 for _, _, steps, _ in calibration),
    )
    residual = sum(
        (Fraction(target) - scale_squared * steps * steps) ** 2
        for _, _, steps, target in validation
    )
    return {
        "calibrated_chain_to_time_squared": _fraction(scale_squared),
        "validation_sum_squared_time2_residual": (
            _fraction(residual) if validation else None
        ),
        "calibration_interval_count": len(calibration),
        "validation_interval_count": len(validation),
        "intervals": [
            {
                "endpoints": [lower, upper],
                "intrinsic_chain_steps": steps,
                "target_time_squared": target,
            }
            for lower, upper, steps, target in samples
        ],
    }


def _residual(fit: dict[str, object] | None, key: str) -> Fraction | None:
    if fit is None or fit[key] is None:
        return None
    return Fraction(*fit[key])


def chain_time_selection_audit(max_size: int = 5) -> dict[str, object]:
    if max_size < 1 or max_size > 5:
        raise ValueError("the exhaustive audit is certified only for 1 <= max_size <= 5")
    rows = []
    first_conflict = None
    for size in range(1, max_size + 1):
        orders = canonical_partial_orders(size)
        ambiguous = time_selected = jointly_selected = conflicts = 0
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
                volume_fit = interval_count_volume_fit(mask, size, coordinates)
                time_fit = chain_time_fit(mask, size, coordinates)
                candidates.append(
                    {
                        "null_rank_coordinates": coordinates,
                        "pairwise_ds2_signature": signature,
                        "volume_fit": volume_fit,
                        "chain_time_fit": time_fit,
                    }
                )
            volume_scores = [
                _residual(c["volume_fit"], "validation_sum_squared_count_residual")
                for c in candidates
            ]
            time_scores = [
                _residual(c["chain_time_fit"], "validation_sum_squared_time2_residual")
                for c in candidates
            ]
            volume_choice = (
                volume_scores.index(min(volume_scores))
                if None not in volume_scores
                and volume_scores.count(min(volume_scores)) == 1
                else None
            )
            time_choice = (
                time_scores.index(min(time_scores))
                if None not in time_scores and time_scores.count(min(time_scores)) == 1
                else None
            )
            if time_choice is not None:
                time_selected += 1
            dominant = []
            if None not in volume_scores and None not in time_scores:
                for index, (volume, time) in enumerate(zip(volume_scores, time_scores)):
                    if all(
                        volume <= other_volume
                        and time <= other_time
                        and (volume < other_volume or time < other_time)
                        for other_index, (other_volume, other_time) in enumerate(
                            zip(volume_scores, time_scores)
                        )
                        if other_index != index
                    ):
                        dominant.append(index)
            if len(dominant) == 1:
                jointly_selected += 1
            if (
                volume_choice is not None
                and time_choice is not None
                and volume_choice != time_choice
            ):
                conflicts += 1
                if first_conflict is None:
                    first_conflict = {
                        "size": size,
                        "order_mask": mask,
                        "volume_choice": volume_choice,
                        "chain_time_choice": time_choice,
                        "candidates": candidates,
                    }
        rows.append(
            {
                "size": size,
                "partial_order_classes": len(orders),
                "metric_ambiguous_classes": ambiguous,
                "uniquely_selected_by_chain_time": time_selected,
                "uniquely_pareto_dominant_jointly": jointly_selected,
                "volume_chain_time_conflicts": conflicts,
            }
        )
    return {
        "program": "MF-MAN-010",
        "scope": "exhaustive up to relabelling for at most five objects",
        "selection_rule": (
            "calibrate squared chain-to-time scale on maximal intrinsic chain "
            "steps, validate on shorter intervals, and combine with volume only "
            "by weight-free Pareto dominance"
        ),
        "external_conventions": [
            "linear-extension ranks are null coordinates",
            "target proper time squared is du*dv",
            "squared residual loss",
            "Pareto comparison assigns no relative volume/time weight",
        ],
        "rows": rows,
        "first_volume_chain_time_conflict": first_conflict,
        "conclusion": (
            "chain-time adds discrimination, but its finite choices conflict with "
            "number-volume and yield no jointly dominant geometry through size five"
        ),
        "claims_not_made": [
            "physical proper time",
            "statistical or continuum convergence",
            "unique emergent geometry",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-size", type=int, default=5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(
        chain_time_selection_audit(args.max_size), indent=2, sort_keys=True
    ) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
