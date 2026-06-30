from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.particle_mesh import leapfrog_particle_mesh_step, particle_mesh_accelerations
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/two_sector_particle_mesh.md")
CSV_PATH = Path("outputs/reports/two_sector_particle_mesh.csv")


def initial_pair(second_sector: Sector) -> list[BodyState]:
    return [
        BodyState(np.asarray([0.35, 0.5]), np.zeros(2), 1.0, Sector.POSITIVE),
        BodyState(np.asarray([0.65, 0.5]), np.zeros(2), 1.0, second_sector),
    ]


def periodic_distance(first: np.ndarray, second: np.ndarray, box_size: float) -> float:
    delta = np.mod(second - first + 0.5 * box_size, box_size) - 0.5 * box_size
    return float(np.linalg.norm(delta))


def run_case(
    second_sector: Sector,
    steps: int = 20,
    dt: float = 0.0005,
    grid_shape: tuple[int, int] = (32, 32),
    box_size: float = 1.0,
) -> list[list[BodyState]]:
    history = [initial_pair(second_sector)]
    bodies = history[0]
    for _ in range(steps):
        bodies = leapfrog_particle_mesh_step(
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
    grid_shape = (32, 32)
    cases = {
        "positive_positive": run_case(Sector.POSITIVE, grid_shape=grid_shape),
        "positive_negative": run_case(Sector.NEGATIVE, grid_shape=grid_shape),
    }

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("case,step,body,sector,x,y,vx,vy\n")
        for case_name, history in cases.items():
            for step, bodies in enumerate(history):
                for body_index, body in enumerate(bodies):
                    handle.write(
                        f"{case_name},{step},{body_index},{body.sector.value},"
                        f"{body.position[0]:.10g},{body.position[1]:.10g},"
                        f"{body.velocity[0]:.10g},{body.velocity[1]:.10g}\n"
                    )

    lines = [
        "# Two-Sector Particle-Mesh Dynamics",
        "",
        "Weak-field periodic particle-mesh diagnostic using CIC deposit/interpolation.",
        "",
        "| case | initial distance | final distance | initial ax body 0 | initial ax body 1 | reading |",
        "|---|---:|---:|---:|---:|---|",
    ]
    for case_name, history in cases.items():
        initial = periodic_distance(history[0][0].position, history[0][1].position, box_size)
        final = periodic_distance(history[-1][0].position, history[-1][1].position, box_size)
        initial_accelerations = particle_mesh_accelerations(
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
            "Boundary: this is a weak-field periodic particle-mesh diagnostic only. It is not a relativistic tensor solver, geodesic integrator, or cosmological N-body simulation.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
