from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.signed_sector import BodyState, Sector, leapfrog_step, total_energy


REPORT_PATH = Path("outputs/reports/two_sector_pair_dynamics.md")
CSV_PATH = Path("outputs/reports/two_sector_pair_dynamics.csv")


def initial_pair(second_sector: Sector) -> list[BodyState]:
    return [
        BodyState(np.asarray([0.0]), np.asarray([0.0]), 1.0, Sector.POSITIVE),
        BodyState(np.asarray([1.0]), np.asarray([0.0]), 1.0, second_sector),
    ]


def distance(bodies: list[BodyState]) -> float:
    return float(abs(bodies[1].position[0] - bodies[0].position[0]))


def run_case(second_sector: Sector, steps: int = 20, dt: float = 0.01) -> list[list[BodyState]]:
    history = [initial_pair(second_sector)]
    bodies = history[0]
    for _ in range(steps):
        bodies = leapfrog_step(bodies, dt=dt, softening=0.02)
        history.append(bodies)
    return history


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    cases = {
        "positive_positive": run_case(Sector.POSITIVE),
        "positive_negative": run_case(Sector.NEGATIVE),
    }

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("case,step,body,sector,x,v\n")
        for case_name, history in cases.items():
            for step, bodies in enumerate(history):
                for body_index, body in enumerate(bodies):
                    handle.write(
                        f"{case_name},{step},{body_index},{body.sector.value},"
                        f"{body.position[0]:.10g},{body.velocity[0]:.10g}\n"
                    )

    lines = [
        "# Two-Sector Pair Dynamics",
        "",
        "Weak-field Janus pair dynamics using `signed_sector.leapfrog_step`.",
        "",
        "| case | initial distance | final distance | energy drift | reading |",
        "|---|---:|---:|---:|---|",
    ]
    for case_name, history in cases.items():
        initial = distance(history[0])
        final = distance(history[-1])
        initial_energy = total_energy(history[0], softening=0.02)
        final_energy = total_energy(history[-1], softening=0.02)
        reading = "approaches" if final < initial else "separates"
        lines.append(
            f"| {case_name} | {initial:.6g} | {final:.6g} | "
            f"{final_energy - initial_energy:.6g} | {reading} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: this is a weak-field N-body consistency check only. It is not a tensor solver, geodesic integrator, or cosmological simulation.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
