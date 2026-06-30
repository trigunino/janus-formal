from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.field_statistics import density_field_summary
from janus_lab.initial_conditions import (
    paired_sector_contrasts_3d,
    sector_contrast_correlation,
    two_sector_lattice_initial_conditions_3d,
)
from janus_lab.particle_mesh_3d import particle_mesh_fields_3d


REPORT_PATH = Path("outputs/reports/gaussian_initial_conditions_3d.md")
CONTRAST_CSV_PATH = Path("outputs/reports/gaussian_initial_conditions_3d_contrasts.csv")


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid_shape = (8, 8, 8)
    box_size = 1.0
    seed = 20260619
    target_rms = 0.05
    spectral_index = 1.0
    displacement_scale = 0.1

    fields = paired_sector_contrasts_3d(
        grid_shape,
        box_size,
        seed=seed,
        target_rms=target_rms,
        spectral_index=spectral_index,
        anti_correlation=1.0,
    )
    bodies = two_sector_lattice_initial_conditions_3d(
        fields,
        box_size=box_size,
        displacement_scale=displacement_scale,
    )
    deposited = particle_mesh_fields_3d(bodies, grid_shape=grid_shape, box_size=box_size)
    deposited_summary = density_field_summary(
        deposited.positive_density_abs,
        deposited.negative_density_abs,
    )

    with CONTRAST_CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("i,j,k,positive_contrast,negative_contrast\n")
        for i in range(grid_shape[0]):
            for j in range(grid_shape[1]):
                for k in range(grid_shape[2]):
                    handle.write(
                        f"{i},{j},{k},{fields.positive_contrast[i, j, k]:.10g},"
                        f"{fields.negative_contrast[i, j, k]:.10g}\n"
                    )

    positive_count = sum(1 for body in bodies if body.sector.value == "positive")
    negative_count = sum(1 for body in bodies if body.sector.value == "negative")
    positive_rms = float(np.sqrt(np.mean(fields.positive_contrast**2)))
    negative_rms = float(np.sqrt(np.mean(fields.negative_contrast**2)))

    lines = [
        "# Gaussian Initial Conditions 3D",
        "",
        "Prototype reproducible 3D initial conditions for two-sector PM diagnostics.",
        "",
        "| metric | value |",
        "|---|---:|",
        f"| seed | {seed} |",
        f"| grid | {grid_shape[0]}x{grid_shape[1]}x{grid_shape[2]} |",
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
        "",
        "Boundary: these are prototype numerical initial conditions. They are not CMB-normalized, not transfer-function calibrated, and not fitted to survey data.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CONTRAST_CSV_PATH}")


if __name__ == "__main__":
    main()
