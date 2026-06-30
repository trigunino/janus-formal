from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import csv
import gc
import time

import numpy as np

from janus_lab.particle_mesh_3d_vectorized import (
    create_two_sector_lattice_state_3d,
    estimate_vectorized_pm_memory_bytes,
    particle_mesh_accelerations_3d_vectorized,
)


REPORT_PATH = Path("outputs/reports/vectorized_pm_3d_progressive_benchmark.md")
CSV_PATH = Path("outputs/reports/vectorized_pm_3d_progressive_benchmark.csv")


def gb(value: int) -> float:
    return value / 1024.0**3


def perturb_negative_sector(state, grid_n: int) -> None:
    negative = state.sector_signs == -1
    state.positions[negative, 0] = (
        state.positions[negative, 0]
        + 0.05 * np.sin(2.0 * np.pi * state.positions[negative, 1])
        + 0.025 * np.sin(2.0 * np.pi * state.positions[negative, 2])
    ) % 1.0


def run_case(grid_n: int) -> dict[str, float]:
    grid_shape = (grid_n, grid_n, grid_n)
    particle_count = 2 * grid_n**3
    estimate_gb = gb(estimate_vectorized_pm_memory_bytes(grid_shape, particle_count))
    state_start = time.perf_counter()
    state = create_two_sector_lattice_state_3d(grid_shape, box_size=1.0)
    perturb_negative_sector(state, grid_n)
    state_seconds = time.perf_counter() - state_start

    accel_start = time.perf_counter()
    accelerations = particle_mesh_accelerations_3d_vectorized(
        state,
        grid_shape,
        box_size=1.0,
    )
    acceleration_seconds = time.perf_counter() - accel_start
    max_acceleration = float(abs(accelerations).max())
    del state
    del accelerations
    gc.collect()
    return {
        "grid_n": float(grid_n),
        "two_sector_particles": float(particle_count),
        "estimated_core_gb": estimate_gb,
        "state_seconds": state_seconds,
        "acceleration_seconds": acceleration_seconds,
        "max_acceleration_abs": max_acceleration,
    }


def parse_args() -> list[int]:
    parser = ArgumentParser()
    parser.add_argument("--grids", nargs="+", type=int, default=[96, 128])
    parser.add_argument("--include-175", action="store_true")
    args = parser.parse_args()
    grids = list(args.grids)
    if args.include_175 and 175 not in grids:
        grids.append(175)
    return grids


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grids = parse_args()
    rows = [run_case(grid_n) for grid_n in grids]

    with CSV_PATH.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    lines = [
        "# Vectorized PM 3D Progressive Benchmark",
        "",
        "Progressive benchmark for the large-grid NumPy PM backend.",
        "",
        "| grid n | particles two-sector | estimated core GB | state build [s] | acceleration [s] | max |a| |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            f"| {int(row['grid_n'])} | {int(row['two_sector_particles'])} | "
            f"{row['estimated_core_gb']:.6g} | {row['state_seconds']:.6g} | "
            f"{row['acceleration_seconds']:.6g} | {row['max_acceleration_abs']:.6g} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: this benchmarks one acceleration evaluation, not a full cosmological run. Use `--include-175` to explicitly test the minimum sigma8 grid.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
