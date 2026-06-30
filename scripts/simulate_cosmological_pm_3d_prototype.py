from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.cosmological_pm import scale_factor_sequence
from janus_lab.cosmological_pm_3d import run_cosmological_pm_3d
from janus_lab.models import JanusExpansion
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/cosmological_pm_3d_prototype.md")
CSV_PATH = Path("outputs/reports/cosmological_pm_3d_prototype.csv")


def initial_pair() -> list[BodyState]:
    return [
        BodyState(np.asarray([0.35, 0.5, 0.5]), np.zeros(3), 1.0, Sector.POSITIVE),
        BodyState(np.asarray([0.65, 0.5, 0.5]), np.zeros(3), 1.0, Sector.NEGATIVE),
    ]


def periodic_distance(first: np.ndarray, second: np.ndarray, box_size: float) -> float:
    delta = np.mod(second - first + 0.5 * box_size, box_size) - 0.5 * box_size
    return float(np.linalg.norm(delta))


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    grid_shape = (16, 16, 16)
    box_size = 1.0
    q0 = -0.087
    steps = 50
    dt = 0.0001
    gravity_scale = 0.2
    scale_factors = scale_factor_sequence(0.5, 1.0, steps)
    redshifts = 1.0 / scale_factors - 1.0
    expansion_rates = np.asarray(JanusExpansion.from_q0(q0).e(redshifts), dtype=float)
    history = run_cosmological_pm_3d(
        initial_pair(),
        dt=dt,
        scale_factors=scale_factors,
        expansion_rates=expansion_rates,
        grid_shape=grid_shape,
        box_size=box_size,
        gravity_scale=gravity_scale,
        hubble_drag=2.0,
    )

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("step,scale_factor,redshift,E,distance\n")
        for step, (state, scale_factor, redshift, expansion_rate) in enumerate(
            zip(history, scale_factors, redshifts, expansion_rates)
        ):
            distance = periodic_distance(state[0].position, state[1].position, box_size)
            handle.write(
                f"{step},{scale_factor:.10g},{redshift:.10g},{expansion_rate:.10g},"
                f"{distance:.10g}\n"
            )

    initial_distance = periodic_distance(history[0][0].position, history[0][1].position, box_size)
    final_distance = periodic_distance(history[-1][0].position, history[-1][1].position, box_size)
    lines = [
        "# Cosmological PM 3D Prototype",
        "",
        "Dimensionless 3D comoving particle-mesh prototype using the Janus expansion background.",
        "",
        "| metric | initial | final | delta |",
        "|---|---:|---:|---:|",
        f"| scale factor | {scale_factors[0]:.6g} | {scale_factors[-1]:.6g} | {scale_factors[-1] - scale_factors[0]:.6g} |",
        f"| redshift | {redshifts[0]:.6g} | {redshifts[-1]:.6g} | {redshifts[-1] - redshifts[0]:.6g} |",
        f"| E(z) | {expansion_rates[0]:.6g} | {expansion_rates[-1]:.6g} | {expansion_rates[-1] - expansion_rates[0]:.6g} |",
        f"| pair distance | {initial_distance:.6g} | {final_distance:.6g} | {final_distance - initial_distance:.6g} |",
        "",
        f"Background: `JanusExpansion.from_q0({q0})`, `a=0.5 -> 1.0`.",
        f"Grid: `{grid_shape[0]}x{grid_shape[1]}x{grid_shape[2]}`, steps: `{steps}`, dt: `{dt}`.",
        f"Numerical gravity scale: `{gravity_scale}`.",
        f"CSV: `{CSV_PATH}`",
        "",
        "Boundary: 3D comoving PM prototype only. This is not calibrated N-body and does not use physical units or survey data.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
