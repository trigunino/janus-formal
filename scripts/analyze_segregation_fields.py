from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.field_statistics import (
    density_field_summary,
    radial_power_spectrum_2d,
    signed_sector_contrast,
)
from janus_lab.particle_mesh import leapfrog_particle_mesh_step, particle_mesh_fields
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/segregation_field_statistics.md")
CSV_PATH = Path("outputs/reports/segregation_field_statistics.csv")
SPECTRUM_CSV_PATH = Path("outputs/reports/segregation_signed_power_spectrum.csv")


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


def run_state(steps: int, dt: float, grid_shape: tuple[int, int], box_size: float) -> list[BodyState]:
    bodies = initial_blobs()
    for _ in range(steps):
        bodies = leapfrog_particle_mesh_step(
            bodies,
            dt=dt,
            grid_shape=grid_shape,
            box_size=box_size,
        )
    return bodies


def summarize_state(
    bodies: list[BodyState],
    grid_shape: tuple[int, int],
    box_size: float,
):
    fields = particle_mesh_fields(bodies, grid_shape=grid_shape, box_size=box_size)
    summary = density_field_summary(fields.positive_density_abs, fields.negative_density_abs)
    signed = signed_sector_contrast(fields.positive_density_abs, fields.negative_density_abs)
    spectrum = radial_power_spectrum_2d(
        signed,
        box_size=box_size,
        bin_edges=2.0 * np.pi * np.asarray([0.5, 1.5, 2.5, 4.5, 8.5, 16.5]),
    )
    return summary, spectrum


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid_shape = (64, 64)
    box_size = 1.0
    dt = 0.00005
    steps = 100
    initial_summary, initial_spectrum = summarize_state(
        run_state(0, dt, grid_shape, box_size),
        grid_shape,
        box_size,
    )
    final_summary, final_spectrum = summarize_state(
        run_state(steps, dt, grid_shape, box_size),
        grid_shape,
        box_size,
    )

    metrics = [
        (
            "positive_contrast_rms",
            initial_summary.positive_contrast_rms,
            final_summary.positive_contrast_rms,
        ),
        (
            "negative_contrast_rms",
            initial_summary.negative_contrast_rms,
            final_summary.negative_contrast_rms,
        ),
        (
            "sector_correlation",
            initial_summary.sector_correlation,
            final_summary.sector_correlation,
        ),
        (
            "signed_contrast_rms",
            initial_summary.signed_contrast_rms,
            final_summary.signed_contrast_rms,
        ),
    ]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("metric,initial,final,delta\n")
        for name, initial, final in metrics:
            handle.write(f"{name},{initial:.10g},{final:.10g},{final - initial:.10g}\n")

    with SPECTRUM_CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("bin,k_center,initial_power,final_power,delta,mode_count\n")
        for index, (k_center, initial_power, final_power, count) in enumerate(
            zip(
                initial_spectrum.k_centers,
                initial_spectrum.power,
                final_spectrum.power,
                final_spectrum.mode_counts,
            )
        ):
            handle.write(
                f"{index},{k_center:.10g},{initial_power:.10g},"
                f"{final_power:.10g},{final_power - initial_power:.10g},{count}\n"
            )

    lines = [
        "# Segregation Field Statistics",
        "",
        "Field-level diagnostics for the deterministic two-sector segregation run.",
        "",
        "| metric | initial | final | delta |",
        "|---|---:|---:|---:|",
    ]
    for name, initial, final in metrics:
        lines.append(f"| {name} | {initial:.6g} | {final:.6g} | {final - initial:.6g} |")
    lines.extend(
        [
            "",
            "| signed contrast k band | initial power | final power | delta |",
            "|---:|---:|---:|---:|",
        ]
    )
    for index, (initial_power, final_power) in enumerate(
        zip(initial_spectrum.power, final_spectrum.power)
    ):
        lines.append(
            f"| {index} | {initial_power:.6g} | {final_power:.6g} | "
            f"{final_power - initial_power:.6g} |"
        )
    lines.extend(
        [
            "",
            f"Grid: `{grid_shape[0]}x{grid_shape[1]}`, steps: `{steps}`, dt: `{dt}`.",
            f"CSV metrics: `{CSV_PATH}`",
            f"CSV spectrum: `{SPECTRUM_CSV_PATH}`",
            "",
            "Boundary: these are internal field diagnostics only. They do not compare to surveys and do not introduce fitted cosmological parameters.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(f"Wrote {SPECTRUM_CSV_PATH}")


if __name__ == "__main__":
    main()
