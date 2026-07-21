"""MF-MAN-007: preregistered Poisson audit for the external Minkowski 1+1 target."""

from __future__ import annotations

import argparse
import bisect
import json
import math
from pathlib import Path

import numpy as np


PROTOCOL = {
    "protocol_id": "MF-MAN-007-v1",
    "base_seed": 20260718,
    "replicates": 64,
    "densities": [256, 1024, 4096],
    "sampling_box_null_coordinates": [[0.0, 1.0], [0.0, 1.0]],
    "equal_volume_regions": [
        {"name": "ratio_1_to_1", "upper": [0.5, 0.5]},
        {"name": "ratio_2_to_1", "upper": [math.sqrt(0.5), math.sqrt(0.125)]},
        {"name": "ratio_4_to_1", "upper": [1.0, 0.25]},
    ],
    "thresholds": {
        "count_mean_relative_error_max": 0.08,
        "count_variance_to_mean_min": 0.60,
        "count_variance_to_mean_max": 1.40,
        "count_three_sigma_coverage_min": 0.95,
        "highest_density_time_relative_bias_max": 0.20,
        "highest_density_directional_spread_relative_max": 0.10,
        "time_bias_must_improve_from_lowest_density": True,
    },
}


def longest_product_chain(points: np.ndarray) -> int:
    """Longest strict product-order chain; ties have probability zero."""
    if len(points) == 0:
        return 0
    ordered = points[np.lexsort((points[:, 1], points[:, 0]))]
    tails: list[float] = []
    for value in ordered[:, 1]:
        index = bisect.bisect_right(tails, float(value))
        if index == len(tails):
            tails.append(float(value))
        else:
            tails[index] = float(value)
    return len(tails)


def one_replicate(density: int, seed: int) -> dict[str, object]:
    rng = np.random.default_rng(seed)
    expected_full_count = density / 2  # target volume of the unit null square
    count = int(rng.poisson(expected_full_count))
    points = rng.random((count, 2))
    regions = []
    for region in PROTOCOL["equal_volume_regions"]:
        upper_u, upper_v = region["upper"]
        selected = points[
            (points[:, 0] <= upper_u) & (points[:, 1] <= upper_v)
        ]
        chain_steps = longest_product_chain(selected) + 1  # include both endpoints
        estimated_time = chain_steps / math.sqrt(2 * density)
        target_time = math.sqrt(upper_u * upper_v)
        regions.append(
            {
                "name": region["name"],
                "count": int(len(selected)),
                "chain_steps": chain_steps,
                "estimated_time": estimated_time,
                "target_time": target_time,
            }
        )
    return {"count": count, "regions": regions}


def _summarize_density(density: int, density_index: int) -> dict[str, object]:
    replicates = int(PROTOCOL["replicates"])
    samples = [
        one_replicate(
            density,
            int(PROTOCOL["base_seed"]) + 100_000 * density_index + replicate,
        )
        for replicate in range(replicates)
    ]
    counts = np.array([sample["count"] for sample in samples], dtype=float)
    expected = density / 2
    mean = float(np.mean(counts))
    variance = float(np.var(counts, ddof=1))
    region_summaries = []
    for region_index, region in enumerate(PROTOCOL["equal_volume_regions"]):
        region_counts = np.array(
            [sample["regions"][region_index]["count"] for sample in samples],
            dtype=float,
        )
        estimates = np.array(
            [sample["regions"][region_index]["estimated_time"] for sample in samples]
        )
        target = float(samples[0]["regions"][region_index]["target_time"])
        expected_region_count = density * float(region["upper"][0] * region["upper"][1]) / 2
        region_count_mean = float(np.mean(region_counts))
        region_count_variance = float(np.var(region_counts, ddof=1))
        estimate_mean = float(np.mean(estimates))
        region_summaries.append(
            {
                "name": region["name"],
                "count": {
                    "expected_mean": expected_region_count,
                    "empirical_mean": region_count_mean,
                    "empirical_variance": region_count_variance,
                    "mean_relative_error": abs(region_count_mean - expected_region_count)
                    / expected_region_count,
                    "variance_to_mean": region_count_variance / expected_region_count,
                    "three_sigma_coverage": float(
                        np.mean(
                            np.abs(region_counts - expected_region_count)
                            <= 3 * math.sqrt(expected_region_count)
                        )
                    ),
                },
                "mean_estimated_time": estimate_mean,
                "target_time": target,
                "relative_bias": abs(estimate_mean - target) / target,
                "standard_error": float(np.std(estimates, ddof=1) / math.sqrt(replicates)),
            }
        )
    time_means = [region["mean_estimated_time"] for region in region_summaries]
    mean_time = sum(time_means) / len(time_means)
    return {
        "density": density,
        "replicates": replicates,
        "full_count": {
            "expected_mean": expected,
            "empirical_mean": mean,
            "empirical_variance": variance,
            "mean_relative_error": abs(mean - expected) / expected,
            "variance_to_mean": variance / expected,
            "three_sigma_coverage": float(
                np.mean(np.abs(counts - expected) <= 3 * math.sqrt(expected))
            ),
        },
        "proper_time": {
            "regions": region_summaries,
            "maximum_relative_bias": max(r["relative_bias"] for r in region_summaries),
            "directional_spread_relative": (max(time_means) - min(time_means)) / mean_time,
        },
    }


def run_audit() -> dict[str, object]:
    results = [
        _summarize_density(density, index)
        for index, density in enumerate(PROTOCOL["densities"])
    ]
    thresholds = PROTOCOL["thresholds"]
    count_summaries = [
        summary
        for row in results
        for summary in (
            [row["full_count"]]
            + [region["count"] for region in row["proper_time"]["regions"]]
        )
    ]
    count_pass = all(
        summary["mean_relative_error"]
        <= thresholds["count_mean_relative_error_max"]
        and thresholds["count_variance_to_mean_min"]
        <= summary["variance_to_mean"]
        <= thresholds["count_variance_to_mean_max"]
        and summary["three_sigma_coverage"]
        >= thresholds["count_three_sigma_coverage_min"]
        for summary in count_summaries
    )
    lowest_bias = results[0]["proper_time"]["maximum_relative_bias"]
    highest_bias = results[-1]["proper_time"]["maximum_relative_bias"]
    time_pass = (
        highest_bias <= thresholds["highest_density_time_relative_bias_max"]
        and results[-1]["proper_time"]["directional_spread_relative"]
        <= thresholds["highest_density_directional_spread_relative_max"]
        and highest_bias < lowest_bias
    )
    return {
        "program": "MF-MAN-007",
        "protocol": PROTOCOL,
        "numpy_version": np.__version__,
        "results": results,
        "gates": {
            "poisson_count_gate": count_pass,
            "chain_time_gate": time_pass,
            "all_preregistered_gates": count_pass and time_pass,
        },
        "scope": "external Minkowski 1+1 simulation; not emergent geometry",
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
