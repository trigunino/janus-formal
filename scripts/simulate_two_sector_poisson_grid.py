from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.poisson import (
    acceleration_from_potential_2d,
    effective_density_grid,
    solve_periodic_poisson_2d,
)
from janus_lab.signed_sector import Sector


REPORT_PATH = Path("outputs/reports/two_sector_poisson_grid.md")
CSV_PATH = Path("outputs/reports/two_sector_poisson_grid.csv")


def periodic_gaussian(
    xx: np.ndarray,
    yy: np.ndarray,
    center_x: float,
    center_y: float,
    sigma: float,
    box_size: float,
) -> np.ndarray:
    dx = np.minimum(np.abs(xx - center_x), box_size - np.abs(xx - center_x))
    dy = np.minimum(np.abs(yy - center_y), box_size - np.abs(yy - center_y))
    return np.exp(-(dx**2 + dy**2) / (2.0 * sigma**2))


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)

    n = 32
    box_size = 1.0
    x = (np.arange(n) + 0.5) * box_size / n
    xx, yy = np.meshgrid(x, x, indexing="ij")
    positive_density = periodic_gaussian(xx, yy, 0.35, 0.5, 0.06, box_size)
    negative_density = periodic_gaussian(xx, yy, 0.65, 0.5, 0.06, box_size)

    rho_plus = effective_density_grid(positive_density, negative_density, Sector.POSITIVE)
    rho_minus = effective_density_grid(positive_density, negative_density, Sector.NEGATIVE)
    phi_plus = solve_periodic_poisson_2d(rho_plus, box_size=box_size)
    phi_minus = solve_periodic_poisson_2d(rho_minus, box_size=box_size)
    ax_plus, ay_plus = acceleration_from_potential_2d(phi_plus, box_size=box_size)
    ax_minus, ay_minus = acceleration_from_potential_2d(phi_minus, box_size=box_size)

    metrics = {
        "max_abs_rho_plus_plus_rho_minus": float(np.max(np.abs(rho_plus + rho_minus))),
        "max_abs_phi_plus_plus_phi_minus": float(np.max(np.abs(phi_plus + phi_minus))),
        "max_abs_ax_plus_plus_ax_minus": float(np.max(np.abs(ax_plus + ax_minus))),
        "max_abs_ay_plus_plus_ay_minus": float(np.max(np.abs(ay_plus + ay_minus))),
        "phi_plus_min": float(np.min(phi_plus)),
        "phi_plus_max": float(np.max(phi_plus)),
    }

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "i,j,x,y,rho_positive_abs,rho_negative_abs,rho_eff_plus,"
            "phi_plus,ax_plus,ay_plus\n"
        )
        for i in range(n):
            for j in range(n):
                handle.write(
                    f"{i},{j},{xx[i, j]:.10g},{yy[i, j]:.10g},"
                    f"{positive_density[i, j]:.10g},{negative_density[i, j]:.10g},"
                    f"{rho_plus[i, j]:.10g},{phi_plus[i, j]:.10g},"
                    f"{ax_plus[i, j]:.10g},{ay_plus[i, j]:.10g}\n"
                )

    lines = [
        "# Two-Sector Periodic Poisson Grid",
        "",
        "Weak-field periodic grid diagnostic for Janus positive/negative density sectors.",
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
            "Boundary: this is a mean-subtracted periodic Poisson diagnostic only. It is not a tensor solver, geodesic integrator, Vlasov solver, or cosmological N-body simulation.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
