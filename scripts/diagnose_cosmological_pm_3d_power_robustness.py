from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.cosmological_pm import scale_factor_sequence
from janus_lab.cosmological_pm_3d import run_cosmological_pm_3d
from janus_lab.field_statistics import radial_power_spectrum_3d, signed_sector_contrast
from janus_lab.initial_conditions import (
    paired_sector_contrasts_3d,
    two_sector_lattice_initial_conditions_3d,
)
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh_3d import particle_mesh_fields_3d


REPORT_PATH = Path("outputs/reports/cosmological_pm_3d_power_robustness.md")
CSV_PATH = Path("outputs/reports/cosmological_pm_3d_power_robustness.csv")


def signed_field(bodies, grid_shape: tuple[int, int, int], box_size: float) -> np.ndarray:
    fields = particle_mesh_fields_3d(bodies, grid_shape=grid_shape, box_size=box_size)
    return signed_sector_contrast(fields.positive_density_abs, fields.negative_density_abs)


def run_case(seed: int, grid_n: int, steps: int = 30) -> dict[str, float]:
    grid_shape = (grid_n, grid_n, grid_n)
    box_size = 1.0
    contrast_fields = paired_sector_contrasts_3d(
        grid_shape,
        box_size,
        seed=seed,
        target_rms=0.05,
        spectral_index=1.0,
        anti_correlation=1.0,
    )
    bodies = two_sector_lattice_initial_conditions_3d(
        contrast_fields,
        box_size=box_size,
        displacement_scale=0.1,
    )
    scale_factors = scale_factor_sequence(0.5, 1.0, steps)
    expansion_rates = np.asarray(
        JanusExpansion.from_q0(-0.087).e(1.0 / scale_factors - 1.0),
        dtype=float,
    )
    history = run_cosmological_pm_3d(
        bodies,
        dt=0.0001,
        scale_factors=scale_factors,
        expansion_rates=expansion_rates,
        grid_shape=grid_shape,
        box_size=box_size,
        gravity_scale=0.5,
        hubble_drag=2.0,
    )
    bin_edges = 2.0 * np.pi * np.asarray([0.5, 1.5, 2.5, 4.5, 8.5])
    initial = radial_power_spectrum_3d(
        signed_field(history[0], grid_shape, box_size),
        box_size=box_size,
        bin_edges=bin_edges,
    )
    final = radial_power_spectrum_3d(
        signed_field(history[-1], grid_shape, box_size),
        box_size=box_size,
        bin_edges=bin_edges,
    )
    initial_total = float(np.sum(initial.power))
    final_total = float(np.sum(final.power))
    return {
        "seed": float(seed),
        "grid_n": float(grid_n),
        "steps": float(steps),
        "initial_total_power": initial_total,
        "final_total_power": final_total,
        "total_growth_ratio": final_total / initial_total,
        "low_k_growth_ratio": float(final.power[0] / initial.power[0]),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = [run_case(seed, grid_n) for seed in (11, 22, 33) for grid_n in (8, 10)]
    passed = [
        row
        for row in rows
        if row["total_growth_ratio"] > 1.0 and row["low_k_growth_ratio"] > 1.0
    ]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "seed,grid_n,steps,initial_total_power,final_total_power,"
            "total_growth_ratio,low_k_growth_ratio\n"
        )
        for row in rows:
            handle.write(
                f"{int(row['seed'])},{int(row['grid_n'])},{int(row['steps'])},"
                f"{row['initial_total_power']:.10g},{row['final_total_power']:.10g},"
                f"{row['total_growth_ratio']:.10g},{row['low_k_growth_ratio']:.10g}\n"
            )

    total_ratios = np.asarray([row["total_growth_ratio"] for row in rows], dtype=float)
    low_k_ratios = np.asarray([row["low_k_growth_ratio"] for row in rows], dtype=float)
    lines = [
        "# Cosmological PM 3D Power Robustness",
        "",
        "Gaussian-IC 3D PM prototype across seeds and grid choices.",
        "",
        f"Passing cases: `{len(passed)}/{len(rows)}`.",
        "",
        "| seed | grid n | total growth | low-k growth |",
        "|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            f"| {int(row['seed'])} | {int(row['grid_n'])} | "
            f"{row['total_growth_ratio']:.6g} | {row['low_k_growth_ratio']:.6g} |"
        )
    lines.extend(
        [
            "",
            f"Median total growth: `{float(np.median(total_ratios)):.6g}`.",
            f"Median low-k growth: `{float(np.median(low_k_ratios)):.6g}`.",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: numerical robustness only on small 3D grids. This is not physical calibration, not survey validation, and not an N-body production run.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
