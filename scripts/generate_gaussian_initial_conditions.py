from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.initial_conditions import (
    paired_sector_contrasts,
    sector_contrast_correlation,
    two_sector_lattice_initial_conditions,
)
from janus_lab.particle_mesh import particle_mesh_fields
from janus_lab.field_statistics import density_field_summary, radial_power_spectrum_2d


REPORT_PATH = Path("outputs/reports/gaussian_initial_conditions.md")
CONTRAST_CSV_PATH = Path("outputs/reports/gaussian_initial_conditions_contrasts.csv")
SPECTRUM_CSV_PATH = Path("outputs/reports/gaussian_initial_conditions_spectrum.csv")


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid_shape = (32, 32)
    box_size = 1.0
    seed = 20260614
    target_rms = 0.05
    spectral_index = 1.0
    displacement_scale = 0.1

    fields = paired_sector_contrasts(
        grid_shape,
        box_size,
        seed=seed,
        target_rms=target_rms,
        spectral_index=spectral_index,
        anti_correlation=1.0,
    )
    bodies = two_sector_lattice_initial_conditions(
        fields,
        box_size=box_size,
        displacement_scale=displacement_scale,
    )
    deposited = particle_mesh_fields(bodies, grid_shape=grid_shape, box_size=box_size)
    deposited_summary = density_field_summary(
        deposited.positive_density_abs,
        deposited.negative_density_abs,
    )
    spectrum = radial_power_spectrum_2d(
        fields.positive_contrast,
        box_size=box_size,
        bin_edges=2.0 * np.pi * np.asarray([0.5, 1.5, 2.5, 4.5, 8.5, 16.5]),
    )

    with CONTRAST_CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("i,j,positive_contrast,negative_contrast\n")
        for i in range(grid_shape[0]):
            for j in range(grid_shape[1]):
                handle.write(
                    f"{i},{j},{fields.positive_contrast[i, j]:.10g},"
                    f"{fields.negative_contrast[i, j]:.10g}\n"
                )

    with SPECTRUM_CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("bin,k_center,power,mode_count\n")
        for index, (k_center, power, count) in enumerate(
            zip(spectrum.k_centers, spectrum.power, spectrum.mode_counts)
        ):
            handle.write(f"{index},{k_center:.10g},{power:.10g},{count}\n")

    positive_count = sum(1 for body in bodies if body.sector.value == "positive")
    negative_count = sum(1 for body in bodies if body.sector.value == "negative")
    positive_rms = float(np.sqrt(np.mean(fields.positive_contrast**2)))
    negative_rms = float(np.sqrt(np.mean(fields.negative_contrast**2)))

    lines = [
        "# Gaussian Initial Conditions",
        "",
        "Prototype reproducible initial conditions for two-sector PM diagnostics.",
        "",
        "| metric | value |",
        "|---|---:|",
        f"| seed | {seed} |",
        f"| grid n | {grid_shape[0]} |",
        f"| target input RMS | {target_rms:.6g} |",
        f"| positive input RMS | {positive_rms:.6g} |",
        f"| negative input RMS | {negative_rms:.6g} |",
        f"| input sector correlation | {sector_contrast_correlation(fields):.6g} |",
        f"| positive particles | {positive_count} |",
        f"| negative particles | {negative_count} |",
        f"| displacement scale | {displacement_scale:.6g} |",
        f"| deposited positive contrast RMS | {deposited_summary.positive_contrast_rms:.6g} |",
        f"| deposited negative contrast RMS | {deposited_summary.negative_contrast_rms:.6g} |",
        f"| deposited sector correlation | {deposited_summary.sector_correlation:.6g} |",
        "",
        f"Contrast CSV: `{CONTRAST_CSV_PATH}`",
        f"Spectrum CSV: `{SPECTRUM_CSV_PATH}`",
        "",
        "Boundary: these are prototype numerical initial conditions. They are not CMB-normalized, not transfer-function calibrated, and not fitted to survey data.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CONTRAST_CSV_PATH}")
    print(f"Wrote {SPECTRUM_CSV_PATH}")


if __name__ == "__main__":
    main()
