from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.particle_mesh_3d import (
    leapfrog_particle_mesh_step_3d,
    particle_mesh_accelerations_3d,
)
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/two_sector_particle_mesh_3d.md")
CSV_PATH = Path("outputs/reports/two_sector_particle_mesh_3d.csv")


def initial_pair(second_sector: Sector) -> list[BodyState]:
    return [
        BodyState(np.asarray([0.35, 0.5, 0.5]), np.zeros(3), 1.0, Sector.POSITIVE),
        BodyState(np.asarray([0.65, 0.5, 0.5]), np.zeros(3), 1.0, second_sector),
    ]


def periodic_distance(first: np.ndarray, second: np.ndarray, box_size: float) -> float:
    delta = np.mod(second - first + 0.5 * box_size, box_size) - 0.5 * box_size
    return float(np.linalg.norm(delta))


def run_case(
    second_sector: Sector,
    steps: int = 20,
    dt: float = 0.0005,
    grid_shape: tuple[int, int, int] = (16, 16, 16),
    box_size: float = 1.0,
) -> list[list[BodyState]]:
    history = [initial_pair(second_sector)]
    bodies = history[0]
    for _ in range(steps):
        bodies = leapfrog_particle_mesh_step_3d(
            bodies,
            dt=dt,
            grid_shape=grid_shape,
            box_size=box_size,
        )
        history.append(bodies)
    return history


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    box_size = 1.0
    grid_shape = (16, 16, 16)
    cases = {
        "positive_positive": run_case(Sector.POSITIVE, grid_shape=grid_shape),
        "positive_negative": run_case(Sector.NEGATIVE, grid_shape=grid_shape),
    }

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("case,step,body,sector,x,y,z,vx,vy,vz\n")
        for case_name, history in cases.items():
            for step, bodies in enumerate(history):
                for body_index, body in enumerate(bodies):
                    handle.write(
                        f"{case_name},{step},{body_index},{body.sector.value},"
                        f"{body.position[0]:.10g},{body.position[1]:.10g},"
                        f"{body.position[2]:.10g},{body.velocity[0]:.10g},"
                        f"{body.velocity[1]:.10g},{body.velocity[2]:.10g}\n"
                    )

    lines = [
        "# Two-Sector Particle-Mesh Dynamics 3D",
        "",
        "Weak-field periodic 3D particle-mesh diagnostic using CIC deposit/interpolation.",
        "",
        "| case | initial distance | final distance | initial ax body 0 | initial ax body 1 | reading |",
        "|---|---:|---:|---:|---:|---|",
    ]
    for case_name, history in cases.items():
        initial = periodic_distance(history[0][0].position, history[0][1].position, box_size)
        final = periodic_distance(history[-1][0].position, history[-1][1].position, box_size)
        initial_accelerations = particle_mesh_accelerations_3d(
            history[0],
            grid_shape=grid_shape,
            box_size=box_size,
        )
        reading = "approaches" if final < initial else "separates"
        lines.append(
            f"| {case_name} | {initial:.6g} | {final:.6g} | "
            f"{initial_accelerations[0][0]:.6g} | {initial_accelerations[1][0]:.6g} | "
            f"{reading} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: this is a weak-field periodic 3D particle-mesh diagnostic only. It is not a calibrated cosmological N-body simulation.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
