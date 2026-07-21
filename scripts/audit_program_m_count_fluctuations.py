"""MF-MAN-014: conformal equal-volume count-fluctuation gate."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_scale_conformal import PROTOCOL as SCALE_PROTOCOL
    from scripts.audit_program_m_scale_conformal import square_grid
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_scale_conformal import PROTOCOL as SCALE_PROTOCOL
    from audit_program_m_scale_conformal import square_grid


PROTOCOL = {
    "protocol_id": "MF-MAN-014-v1",
    "base_seed": 2026101400,
    "physical_densities": SCALE_PROTOCOL["physical_densities"],
    "bins_per_null_axis": 4,
    "equal_volume_cells": 16,
    "calibration_replicates": 199,
    "validation_replicates": 400,
    "alpha": 0.10,
    "lower_rank": 10,
    "upper_rank": 190,
}


def count_fano_factor(points: np.ndarray, bins: int = 4) -> float:
    counts = np.histogram2d(
        points[:, 0], points[:, 1], bins=bins, range=[[0.0, 1.0], [0.0, 1.0]]
    )[0].ravel()
    mean = float(np.mean(counts))
    return float(np.var(counts, ddof=1) / mean) if mean > 0 else 0.0


def poisson_fano(density: int, seed: int) -> float:
    rng = np.random.default_rng(seed)
    points = rng.random((int(rng.poisson(density / 2)), 2))
    return count_fano_factor(points, int(PROTOCOL["bins_per_null_axis"]))


def diagonal_control(density: int) -> np.ndarray:
    count = density // 2
    axis = (np.arange(count, dtype=float) + 0.5) / count
    return np.column_stack((axis, axis))


def count_fluctuation_audit() -> dict[str, object]:
    calibration_count = int(PROTOCOL["calibration_replicates"])
    validation_count = int(PROTOCOL["validation_replicates"])
    lower_rank = int(PROTOCOL["lower_rank"])
    upper_rank = int(PROTOCOL["upper_rank"])
    rows = []
    for density_index, density in enumerate(PROTOCOL["physical_densities"]):
        seed_root = int(PROTOCOL["base_seed"]) + 100_000 * density_index
        calibration = sorted(
            poisson_fano(density, seed_root + replicate)
            for replicate in range(calibration_count)
        )
        lower = calibration[lower_rank - 1]
        upper = calibration[upper_rank - 1]
        validation = np.array(
            [
                poisson_fano(density, seed_root + 50_000 + replicate)
                for replicate in range(validation_count)
            ]
        )
        grid_fano = count_fano_factor(square_grid(density))
        diagonal_fano = count_fano_factor(diagonal_control(density))
        rows.append(
            {
                "physical_density": density,
                "acceptance_interval": [lower, upper],
                "validation_coverage": float(
                    np.mean((lower <= validation) & (validation <= upper))
                ),
                "validation_mean_fano": float(np.mean(validation)),
                "square_grid_control": {
                    "fano_factor": grid_fano,
                    "accepted": lower <= grid_fano <= upper,
                },
                "diagonal_control": {
                    "fano_factor": diagonal_fano,
                    "accepted": lower <= diagonal_fano <= upper,
                },
            }
        )
    return {
        "program": "MF-MAN-014",
        "protocol": PROTOCOL,
        "statistic": (
            "sample variance divided by sample mean across sixteen equal-volume "
            "null-coordinate cells"
        ),
        "guarantee": (
            "90% marginal two-sided split-conformal coverage at each density "
            "under exchangeability; not simultaneous or conditional coverage"
        ),
        "protocol_integrity": {
            "rank_tail_probability": [10, 200],
            "central_coverage": 0.90,
            "fresh_validation_seeds": True,
            "thresholds_fixed_before_controls": True,
        },
        "rows": rows,
        "negative_control_gate": {
            "all_square_grids_rejected": all(
                not row["square_grid_control"]["accepted"] for row in rows
            ),
            "all_diagonal_controls_rejected": all(
                not row["diagonal_control"]["accepted"] for row in rows
            ),
        },
        "combined_with_mf_man_013": {
            "square_grid_scale_consistency_collision": True,
            "square_grid_rejected_by_fluctuations": all(
                not row["square_grid_control"]["accepted"] for row in rows
            ),
            "status": "tested_controls_separated",
        },
        "claims_not_made": [
            "coordinate-free or Lorentz-invariant reconstruction",
            "sufficiency against untested adversaries",
            "emergent geometry, physical causality or a throat",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(count_fluctuation_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
