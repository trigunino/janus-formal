from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.poisson import (
    acceleration_from_potential_3d,
    effective_density_grid,
    solve_periodic_poisson_3d,
)
from janus_lab.signed_sector import Sector


REPORT_PATH = Path("outputs/reports/two_sector_poisson_grid_3d.md")
CSV_PATH = Path("outputs/reports/two_sector_poisson_grid_3d.csv")


def periodic_gaussian_3d(
    xx: np.ndarray,
    yy: np.ndarray,
    zz: np.ndarray,
    center: tuple[float, float, float],
    sigma: float,
    box_size: float,
) -> np.ndarray:
    dx = np.minimum(np.abs(xx - center[0]), box_size - np.abs(xx - center[0]))
    dy = np.minimum(np.abs(yy - center[1]), box_size - np.abs(yy - center[1]))
    dz = np.minimum(np.abs(zz - center[2]), box_size - np.abs(zz - center[2]))
    return np.exp(-(dx**2 + dy**2 + dz**2) / (2.0 * sigma**2))


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    n = 16
    box_size = 1.0
    x = (np.arange(n) + 0.5) * box_size / n
    xx, yy, zz = np.meshgrid(x, x, x, indexing="ij")
    positive_density = periodic_gaussian_3d(xx, yy, zz, (0.35, 0.5, 0.5), 0.07, box_size)
    negative_density = periodic_gaussian_3d(xx, yy, zz, (0.65, 0.5, 0.5), 0.07, box_size)

    rho_plus = effective_density_grid(positive_density, negative_density, Sector.POSITIVE)
    rho_minus = effective_density_grid(positive_density, negative_density, Sector.NEGATIVE)
    phi_plus = solve_periodic_poisson_3d(rho_plus, box_size=box_size)
    phi_minus = solve_periodic_poisson_3d(rho_minus, box_size=box_size)
    ax_plus, ay_plus, az_plus = acceleration_from_potential_3d(phi_plus, box_size=box_size)
    ax_minus, ay_minus, az_minus = acceleration_from_potential_3d(phi_minus, box_size=box_size)

    metrics = {
        "max_abs_rho_plus_plus_rho_minus": float(np.max(np.abs(rho_plus + rho_minus))),
        "max_abs_phi_plus_plus_phi_minus": float(np.max(np.abs(phi_plus + phi_minus))),
        "max_abs_ax_plus_plus_ax_minus": float(np.max(np.abs(ax_plus + ax_minus))),
        "max_abs_ay_plus_plus_ay_minus": float(np.max(np.abs(ay_plus + ay_minus))),
        "max_abs_az_plus_plus_az_minus": float(np.max(np.abs(az_plus + az_minus))),
        "phi_plus_min": float(np.min(phi_plus)),
        "phi_plus_max": float(np.max(phi_plus)),
    }

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("metric,value\n")
        for name, value in metrics.items():
            handle.write(f"{name},{value:.10g}\n")

    lines = [
        "# Two-Sector Periodic Poisson Grid 3D",
        "",
        "Weak-field periodic 3D grid diagnostic for Janus positive/negative density sectors.",
        "",
        "| metric | value |",
        "|---|---:|",
    ]
    for name, value in metrics.items():
        lines.append(f"| {name} | {value:.6g} |")
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: this is a 3D Poisson diagnostic only. It is not yet 3D particle-mesh evolution or calibrated cosmological N-body.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
