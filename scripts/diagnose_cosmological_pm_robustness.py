from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.cosmological_pm import run_cosmological_pm, scale_factor_sequence
from janus_lab.field_statistics import density_field_summary
from janus_lab.models import JanusExpansion
from janus_lab.particle_mesh import particle_mesh_fields, segregation_metrics
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/cosmological_pm_robustness.md")
CSV_PATH = Path("outputs/reports/cosmological_pm_robustness.csv")


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


def run_case(
    grid_n: int,
    dt: float,
    q0: float = -0.087,
    gravity_scale: float = 0.1,
    total_time: float = 0.005,
) -> dict[str, float]:
    grid_shape = (grid_n, grid_n)
    box_size = 1.0
    steps = int(round(total_time / dt))
    scale_factors = scale_factor_sequence(0.5, 1.0, steps)
    redshifts = 1.0 / scale_factors - 1.0
    expansion_rates = np.asarray(JanusExpansion.from_q0(q0).e(redshifts), dtype=float)
    initial = initial_blobs()
    history = run_cosmological_pm(
        initial,
        dt=dt,
        scale_factors=scale_factors,
        expansion_rates=expansion_rates,
        grid_shape=grid_shape,
        box_size=box_size,
        gravity_scale=gravity_scale,
        hubble_drag=2.0,
    )
    initial_metrics = segregation_metrics(history[0], box_size)
    final_metrics = segregation_metrics(history[-1], box_size)
    return {
        "grid_n": float(grid_n),
        "dt": dt,
        "steps": float(steps),
        "delta_cross": final_metrics.cross_sector_distance - initial_metrics.cross_sector_distance,
        "delta_ratio": final_metrics.segregation_ratio - initial_metrics.segregation_ratio,
        "delta_signed_rms": signed_rms(history[-1], grid_shape, box_size)
        - signed_rms(history[0], grid_shape, box_size),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = [run_case(grid_n, dt) for grid_n in (32, 48, 64) for dt in (0.000025, 0.00005, 0.0001)]
    passed = [
        row
        for row in rows
        if row["delta_cross"] > 0.0
        and row["delta_ratio"] > 0.0
        and row["delta_signed_rms"] > 0.0
    ]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("grid_n,dt,steps,delta_cross,delta_ratio,delta_signed_rms\n")
        for row in rows:
            handle.write(
                f"{int(row['grid_n'])},{row['dt']:.10g},{int(row['steps'])},"
                f"{row['delta_cross']:.10g},{row['delta_ratio']:.10g},"
                f"{row['delta_signed_rms']:.10g}\n"
            )

    lines = [
        "# Cosmological PM Robustness Diagnostic",
        "",
        "Comoving Janus-background PM prototype across grid and time-step choices.",
        "",
        f"Passing cases: `{len(passed)}/{len(rows)}`.",
        "",
        "| grid n | dt | steps | delta cross | delta ratio | delta signed RMS |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            f"| {int(row['grid_n'])} | {row['dt']:.6g} | {int(row['steps'])} | "
            f"{row['delta_cross']:.6g} | {row['delta_ratio']:.6g} | "
            f"{row['delta_signed_rms']:.6g} |"
        )
    lines.extend(
        [
            "",
            "Background: `JanusExpansion.from_q0(-0.087)`, `a=0.5 -> 1.0`, gravity scale `0.1`.",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: prototype numerical robustness only. This is not calibrated N-body, not a survey comparison, and not a physical parameter fit.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
