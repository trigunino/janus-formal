from __future__ import annotations

from pathlib import Path
import time

import numpy as np

from janus_lab.particle_mesh_3d_vectorized import (
    create_two_sector_lattice_state_3d,
    estimate_vectorized_pm_memory_bytes,
    particle_mesh_accelerations_3d_vectorized,
)


REPORT_PATH = Path("outputs/reports/vectorized_pm_3d_benchmark.md")


def gb(value: int) -> float:
    return value / 1024.0**3


def run_case(grid_n: int) -> dict[str, float]:
    state = create_two_sector_lattice_state_3d((grid_n, grid_n, grid_n), box_size=1.0)
    negative = state.sector_signs == -1
    state.positions[negative, 0] = (
        state.positions[negative, 0]
        + 0.05 * np.sin(2.0 * np.pi * state.positions[negative, 1])
    ) % 1.0
    start = time.perf_counter()
    accelerations = particle_mesh_accelerations_3d_vectorized(
        state,
        (grid_n, grid_n, grid_n),
        box_size=1.0,
    )
    elapsed = time.perf_counter() - start
    return {
        "grid_n": float(grid_n),
        "two_sector_particles": float(len(state.positions)),
        "elapsed_seconds": elapsed,
        "max_acceleration_abs": float(abs(accelerations).max()),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    measured = [run_case(grid_n) for grid_n in (16, 32, 64)]
    estimates = []
    for grid_n in (64, 128, 175, 350):
        particle_count = 2 * grid_n**3
        estimates.append(
            {
                "grid_n": grid_n,
                "two_sector_particles": particle_count,
                "estimated_gb": gb(
                    estimate_vectorized_pm_memory_bytes(
                        (grid_n, grid_n, grid_n),
                        particle_count=particle_count,
                    )
                ),
            }
        )

    lines = [
        "# Vectorized PM 3D Benchmark",
        "",
        "Backend NumPy vectorise pour remplacer les objets `BodyState` sur les grandes grilles.",
        "",
        "| measured grid n | particles two-sector | acceleration step [s] | max |a| |",
        "|---:|---:|---:|---:|",
    ]
    for row in measured:
        lines.append(
            f"| {int(row['grid_n'])} | {int(row['two_sector_particles'])} | "
            f"{row['elapsed_seconds']:.6g} | {row['max_acceleration_abs']:.6g} |"
        )
    lines.extend(
        [
            "",
            "| estimated grid n | particles two-sector | estimated core memory [GB] |",
            "|---:|---:|---:|",
        ]
    )
    for row in estimates:
        lines.append(
            f"| {row['grid_n']} | {row['two_sector_particles']} | {row['estimated_gb']:.6g} |"
        )
    lines.extend(
        [
            "",
            "Boundary: estimates cover core NumPy arrays, not all FFT temporaries or OS overhead. Increase grid size progressively.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")


if __name__ == "__main__":
    main()
