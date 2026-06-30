from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import csv
import time

import numpy as np

from janus_lab.cosmological_pm import scale_factor_sequence
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh_3d_vectorized import (
    cosmological_pm_step_3d_vectorized,
    create_two_sector_lattice_state_3d,
    estimate_vectorized_pm_memory_bytes,
)


REPORT_PATH = Path("outputs/reports/vectorized_pm_3d_short_stability.md")
CSV_PATH = Path("outputs/reports/vectorized_pm_3d_short_stability.csv")


def gb(value: int) -> float:
    return value / 1024.0**3


def perturb_negative_sector(state) -> None:
    negative = state.sector_signs == -1
    state.positions[negative, 0] = (
        state.positions[negative, 0]
        + 0.05 * np.sin(2.0 * np.pi * state.positions[negative, 1])
        + 0.025 * np.sin(2.0 * np.pi * state.positions[negative, 2])
    ) % 1.0


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--grid", type=int, default=128)
    parser.add_argument("--steps", type=int, default=3)
    parser.add_argument("--dt", type=float, default=0.0001)
    parser.add_argument("--gravity-scale", type=float, default=0.5)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.grid <= 0:
        raise ValueError("--grid must be positive.")
    if args.steps <= 0:
        raise ValueError("--steps must be positive.")
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)

    grid_shape = (args.grid, args.grid, args.grid)
    particle_count = 2 * args.grid**3
    estimated_gb = gb(estimate_vectorized_pm_memory_bytes(grid_shape, particle_count))

    build_start = time.perf_counter()
    state = create_two_sector_lattice_state_3d(grid_shape, box_size=1.0)
    perturb_negative_sector(state)
    build_seconds = time.perf_counter() - build_start

    scale_factors = scale_factor_sequence(0.5, 1.0, args.steps)
    expansion_rates = np.asarray(
        JanusExpansion.from_q0(-0.087).e(1.0 / scale_factors - 1.0),
        dtype=float,
    )

    rows = []
    total_start = time.perf_counter()
    for step, (scale_factor, expansion_rate) in enumerate(
        zip(scale_factors[:-1], expansion_rates[:-1]),
        start=1,
    ):
        positions_before = state.positions.copy()
        step_start = time.perf_counter()
        state = cosmological_pm_step_3d_vectorized(
            state,
            dt=args.dt,
            scale_factor=float(scale_factor),
            expansion_rate=float(expansion_rate),
            grid_shape=grid_shape,
            box_size=1.0,
            gravity_scale=args.gravity_scale,
            in_place=True,
        )
        elapsed = time.perf_counter() - step_start
        displacement = np.mod(state.positions - positions_before + 0.5, 1.0) - 0.5
        rows.append(
            {
                "step": step,
                "scale_factor": float(scale_factor),
                "expansion_rate": float(expansion_rate),
                "seconds": elapsed,
                "max_speed": float(np.linalg.norm(state.velocities, axis=1).max()),
                "max_step_displacement": float(np.linalg.norm(displacement, axis=1).max()),
                "finite": bool(np.isfinite(state.positions).all() and np.isfinite(state.velocities).all()),
            }
        )
        del positions_before
    total_seconds = time.perf_counter() - total_start

    with CSV_PATH.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    passed = all(row["finite"] for row in rows)
    lines = [
        "# Vectorized PM 3D Short Stability",
        "",
        "Short multi-step stability run for the large-grid vectorized PM backend.",
        "",
        "| metric | value |",
        "|---|---:|",
        f"| grid | {args.grid}^3 |",
        f"| two-sector particles | {particle_count} |",
        f"| estimated core memory | {estimated_gb:.6g} GB |",
        f"| state build | {build_seconds:.6g} s |",
        f"| requested steps | {args.steps} |",
        f"| completed PM steps | {len(rows)} |",
        f"| total step time | {total_seconds:.6g} s |",
        f"| finite state | {passed} |",
        "",
        "| step | a | E | seconds | max speed | max step displacement | finite |",
        "|---:|---:|---:|---:|---:|---:|---|",
    ]
    for row in rows:
        lines.append(
            f"| {row['step']} | {row['scale_factor']:.6g} | {row['expansion_rate']:.6g} | "
            f"{row['seconds']:.6g} | {row['max_speed']:.6g} | "
            f"{row['max_step_displacement']:.6g} | {row['finite']} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: this checks short numerical stability only. It is not a sigma8-normalized physical production run.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
