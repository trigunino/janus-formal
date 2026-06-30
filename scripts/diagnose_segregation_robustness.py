from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.field_statistics import density_field_summary
from janus_lab.particle_mesh import (
    leapfrog_particle_mesh_step,
    particle_mesh_fields,
    segregation_metrics,
)
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/segregation_robustness.md")
CSV_PATH = Path("outputs/reports/segregation_robustness.csv")


def initial_blobs() -> list[BodyState]:
    bodies: list[BodyState] = []
    offsets = (-0.03, -0.01, 0.01, 0.03)
    for dx in offsets:
        for dy in offsets:
            bodies.append(
                BodyState(np.asarray([0.42 + dx, 0.5 + dy]), np.zeros(2), 1.0, Sector.POSITIVE)
            )
            bodies.append(
                BodyState(np.asarray([0.58 + dx, 0.5 + dy]), np.zeros(2), 1.0, Sector.NEGATIVE)
            )
    return bodies


def signed_rms(bodies: list[BodyState], grid_shape: tuple[int, int], box_size: float) -> float:
    fields = particle_mesh_fields(bodies, grid_shape=grid_shape, box_size=box_size)
    return density_field_summary(
        fields.positive_density_abs,
        fields.negative_density_abs,
    ).signed_contrast_rms


def run_case(grid_n: int, dt: float, total_time: float = 0.005) -> dict[str, float]:
    grid_shape = (grid_n, grid_n)
    box_size = 1.0
    steps = int(round(total_time / dt))
    bodies = initial_blobs()
    initial_metrics = segregation_metrics(bodies, box_size)
    initial_signed_rms = signed_rms(bodies, grid_shape, box_size)
    for _ in range(steps):
        bodies = leapfrog_particle_mesh_step(
            bodies,
            dt=dt,
            grid_shape=grid_shape,
            box_size=box_size,
        )
    final_metrics = segregation_metrics(bodies, box_size)
    final_signed_rms = signed_rms(bodies, grid_shape, box_size)
    return {
        "grid_n": float(grid_n),
        "dt": dt,
        "steps": float(steps),
        "delta_cross_distance": final_metrics.cross_sector_distance
        - initial_metrics.cross_sector_distance,
        "delta_segregation_ratio": final_metrics.segregation_ratio
        - initial_metrics.segregation_ratio,
        "delta_signed_contrast_rms": final_signed_rms - initial_signed_rms,
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = [run_case(grid_n, dt) for grid_n in (32, 48, 64) for dt in (0.000025, 0.00005, 0.0001)]
    passed = [
        row
        for row in rows
        if row["delta_cross_distance"] > 0.0
        and row["delta_segregation_ratio"] > 0.0
        and row["delta_signed_contrast_rms"] > 0.0
    ]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "grid_n,dt,steps,delta_cross_distance,"
            "delta_segregation_ratio,delta_signed_contrast_rms\n"
        )
        for row in rows:
            handle.write(
                f"{int(row['grid_n'])},{row['dt']:.10g},{int(row['steps'])},"
                f"{row['delta_cross_distance']:.10g},"
                f"{row['delta_segregation_ratio']:.10g},"
                f"{row['delta_signed_contrast_rms']:.10g}\n"
            )

    lines = [
        "# Segregation Robustness Diagnostic",
        "",
        "Same deterministic two-sector blobs evolved to fixed total time across grid and time-step choices.",
        "",
        f"Passing cases: `{len(passed)}/{len(rows)}`.",
        "",
        "| grid n | dt | steps | delta cross distance | delta segregation ratio | delta signed contrast RMS |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            f"| {int(row['grid_n'])} | {row['dt']:.6g} | {int(row['steps'])} | "
            f"{row['delta_cross_distance']:.6g} | "
            f"{row['delta_segregation_ratio']:.6g} | "
            f"{row['delta_signed_contrast_rms']:.6g} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: this is a numerical robustness check only. It is not a parameter fit, survey comparison, or proof of the full cosmological model.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
