from __future__ import annotations

from pathlib import Path
import json

from janus_lab.physical_units import PhysicalBoxCalibration


REPORT_PATH = Path("outputs/reports/physical_pm_box_calibration.md")
JSON_PATH = Path("outputs/reports/physical_pm_box_calibration.json")


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    calibration = PhysicalBoxCalibration.from_total_absolute_omega(
        box_size_mpc=1000.0,
        grid_shape=(8, 8, 8),
        h0_km_s_mpc=70.0,
        omega_abs=0.315,
        positive_fraction=0.5,
    )

    payload = {
        "box_size_mpc": calibration.box_size_mpc,
        "grid_shape": list(calibration.grid_shape),
        "h0_km_s_mpc": calibration.h0_km_s_mpc,
        "h": calibration.h,
        "positive_omega_abs": calibration.positive_omega_abs,
        "negative_omega_abs": calibration.negative_omega_abs,
        "critical_density_msun_mpc3": calibration.critical_density_msun_mpc3,
        "total_abs_density_msun_mpc3": calibration.total_abs_density_msun_mpc3,
        "cell_size_mpc": list(calibration.cell_size_mpc),
        "particle_count_per_sector": calibration.particle_count_per_sector,
        "positive_particle_mass_msun": calibration.positive_particle_mass_msun,
        "negative_abs_particle_mass_msun": calibration.negative_abs_particle_mass_msun,
        "fundamental_mode_inv_mpc": calibration.fundamental_mode_inv_mpc,
        "nyquist_mode_inv_mpc": calibration.nyquist_mode_inv_mpc,
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Physical PM Box Calibration",
        "",
        "Minimal physical interpretation layer for the current dimensionless 3D PM prototype.",
        "",
        "| metric | value |",
        "|---|---:|",
        f"| box size | {calibration.box_size_mpc:.6g} Mpc |",
        (
            f"| grid | {calibration.grid_shape[0]}x{calibration.grid_shape[1]}x"
            f"{calibration.grid_shape[2]} |"
        ),
        f"| cell size | {calibration.cell_size_mpc[0]:.6g} Mpc |",
        f"| H0 | {calibration.h0_km_s_mpc:.6g} km/s/Mpc |",
        f"| h | {calibration.h:.6g} |",
        f"| positive Omega abs | {calibration.positive_omega_abs:.6g} |",
        f"| negative Omega abs | {calibration.negative_omega_abs:.6g} |",
        f"| rho crit | {calibration.critical_density_msun_mpc3:.6g} Msun/Mpc^3 |",
        f"| total abs density | {calibration.total_abs_density_msun_mpc3:.6g} Msun/Mpc^3 |",
        f"| particles per sector | {calibration.particle_count_per_sector} |",
        f"| positive particle mass | {calibration.positive_particle_mass_msun:.6g} Msun |",
        f"| negative abs particle mass | {calibration.negative_abs_particle_mass_msun:.6g} Msun |",
        f"| k fundamental | {calibration.fundamental_mode_inv_mpc:.6g} 1/Mpc |",
        f"| k Nyquist | {calibration.nyquist_mode_inv_mpc:.6g} 1/Mpc |",
        "",
        f"JSON: `{JSON_PATH}`",
        "",
        "Boundary: this calibrates scales only. The current PM evolution remains dimensionless and is not yet a physical N-body integrator.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
