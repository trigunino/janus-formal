from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/sigma8_resolution_requirements.md")
JSON_PATH = Path("outputs/reports/sigma8_resolution_requirements.json")


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    calibration = PhysicalBoxCalibration.from_total_absolute_omega(
        box_size_mpc=1000.0,
        grid_shape=(8, 8, 8),
        h0_km_s_mpc=70.0,
        omega_abs=0.315,
        positive_fraction=0.5,
    )
    radius = calibration.sigma8_radius_mpc
    k_radius = 2.0 * np.pi / radius
    rows = []
    for cells_per_radius in (2.0, 4.0, 8.0):
        grid_n = calibration.grid_n_required_for_radius(
            radius,
            cells_per_radius=cells_per_radius,
        )
        particles_per_sector = grid_n**3
        rows.append(
            {
                "cells_per_radius": cells_per_radius,
                "grid_n": grid_n,
                "cell_size_mpc": calibration.box_size_mpc / grid_n,
                "particles_per_sector": particles_per_sector,
                "two_sector_particles": 2 * particles_per_sector,
            }
        )

    payload = {
        "box_size_mpc": calibration.box_size_mpc,
        "current_grid_shape": list(calibration.grid_shape),
        "current_cell_size_mpc": list(calibration.cell_size_mpc),
        "h0_km_s_mpc": calibration.h0_km_s_mpc,
        "sigma8_radius_mpc": radius,
        "sigma8_k_radius_inv_mpc": k_radius,
        "current_nyquist_inv_mpc": calibration.nyquist_mode_inv_mpc,
        "current_resolves_sigma8": calibration.resolves_radius(radius),
        "requirements": rows,
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Sigma8 Resolution Requirements",
        "",
        "Resolution check before attempting physical `sigma8` normalization.",
        "",
        "| metric | value |",
        "|---|---:|",
        f"| box size | {calibration.box_size_mpc:.6g} Mpc |",
        (
            f"| current grid | {calibration.grid_shape[0]}x{calibration.grid_shape[1]}x"
            f"{calibration.grid_shape[2]} |"
        ),
        f"| current cell size | {calibration.cell_size_mpc[0]:.6g} Mpc |",
        f"| H0 | {calibration.h0_km_s_mpc:.6g} km/s/Mpc |",
        f"| sigma8 radius | {radius:.6g} Mpc |",
        f"| sigma8 scale k=2pi/R | {k_radius:.6g} 1/Mpc |",
        f"| current k Nyquist | {calibration.nyquist_mode_inv_mpc:.6g} 1/Mpc |",
        f"| current resolves sigma8 | {calibration.resolves_radius(radius)} |",
        "",
        "| cells per radius | required grid n | cell size [Mpc] | particles per sector | two-sector particles |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            f"| {row['cells_per_radius']:.0f} | {row['grid_n']} | "
            f"{row['cell_size_mpc']:.6g} | {row['particles_per_sector']} | "
            f"{row['two_sector_particles']} |"
        )
    lines.extend(
        [
            "",
            f"JSON: `{JSON_PATH}`",
            "",
            "Conclusion: the current 8^3 grid cannot support a defensible sigma8 normalization. Use this only after moving to at least the required grid scale, or normalize only long-wavelength bands explicitly marked as such.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
