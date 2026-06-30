from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.quantum_sector import (
    BoundaryCondition,
    JanusQuantumState1D,
    expectation_value_1d,
    gaussian_wavepacket_1d,
    quantum_mass_densities_1d,
    run_schrodinger_poisson_1d,
    schrodinger_hamiltonian_1d,
    schrodinger_poisson_energy_1d,
    schrodinger_poisson_step_1d,
    sector_centroid_separation_1d,
    sector_probability_1d,
    solve_periodic_poisson_1d,
    unitary_step_1d,
)


REPORT_PATH = Path("outputs/reports/quantum_janus_1d.md")
CSV_PATH = Path("outputs/reports/quantum_janus_1d.csv")


def initial_state(grid_n: int = 96, box_half_width: float = 8.0) -> JanusQuantumState1D:
    grid = np.linspace(-box_half_width, box_half_width, grid_n, endpoint=False)
    return JanusQuantumState1D(
        grid,
        gaussian_wavepacket_1d(grid, center=-1.0, width=0.7),
        gaussian_wavepacket_1d(grid, center=1.0, width=0.7),
        mass_abs=1.0,
    )


def all_attractive_energy(state: JanusQuantumState1D, gravitational_constant: float) -> float:
    x = state.grid
    dx = float(x[1] - x[0])
    rho_positive, rho_negative = quantum_mass_densities_1d(state)
    phi = solve_periodic_poisson_1d(
        x,
        rho_positive + rho_negative,
        gravitational_constant=gravitational_constant,
    )
    kinetic = schrodinger_hamiltonian_1d(
        x,
        state.mass_abs,
        hbar=state.hbar,
        boundary_condition=BoundaryCondition.PERIODIC,
    )
    kinetic_energy = expectation_value_1d(x, state.positive, kinetic)
    kinetic_energy += expectation_value_1d(x, state.negative, kinetic)
    potential_energy = 0.5 * np.sum((rho_positive + rho_negative) * phi) * dx
    energy = kinetic_energy + potential_energy
    if abs(energy.imag) > 1e-10:
        raise ValueError("control energy has a non-negligible imaginary part.")
    return float(energy.real)


def all_attractive_step(
    state: JanusQuantumState1D,
    dt: float,
    gravitational_constant: float,
) -> JanusQuantumState1D:
    rho_positive, rho_negative = quantum_mass_densities_1d(state)
    phi = solve_periodic_poisson_1d(
        state.grid,
        rho_positive + rho_negative,
        gravitational_constant=gravitational_constant,
    )
    hamiltonian = schrodinger_hamiltonian_1d(
        state.grid,
        state.mass_abs,
        potential_energy=state.mass_abs * phi,
        hbar=state.hbar,
        boundary_condition=BoundaryCondition.PERIODIC,
    )
    return JanusQuantumState1D(
        state.grid,
        unitary_step_1d(state.positive, hamiltonian, dt, hbar=state.hbar),
        unitary_step_1d(state.negative, hamiltonian, dt, hbar=state.hbar),
        state.mass_abs,
        hbar=state.hbar,
    )


def run_all_attractive_control(
    state: JanusQuantumState1D,
    steps: int,
    dt: float,
    gravitational_constant: float,
) -> dict[str, np.ndarray | JanusQuantumState1D]:
    current = state
    energies: list[float] = []
    positive_probabilities: list[float] = []
    negative_probabilities: list[float] = []
    separations: list[float] = []
    for step in range(steps + 1):
        energies.append(all_attractive_energy(current, gravitational_constant))
        positive_probabilities.append(sector_probability_1d(current.grid, current.positive))
        negative_probabilities.append(sector_probability_1d(current.grid, current.negative))
        separations.append(sector_centroid_separation_1d(current))
        if step < steps:
            current = all_attractive_step(current, dt, gravitational_constant)
    return {
        "final_state": current,
        "energies": np.asarray(energies, dtype=float),
        "positive_probabilities": np.asarray(positive_probabilities, dtype=float),
        "negative_probabilities": np.asarray(negative_probabilities, dtype=float),
        "sector_separations": np.asarray(separations, dtype=float),
    }


def summarize_run(name: str, run: object) -> dict[str, float | str]:
    energies = np.asarray(getattr(run, "energies") if hasattr(run, "energies") else run["energies"])
    positive_probabilities = np.asarray(
        getattr(run, "positive_probabilities")
        if hasattr(run, "positive_probabilities")
        else run["positive_probabilities"]
    )
    negative_probabilities = np.asarray(
        getattr(run, "negative_probabilities")
        if hasattr(run, "negative_probabilities")
        else run["negative_probabilities"]
    )
    separations = np.asarray(
        getattr(run, "sector_separations")
        if hasattr(run, "sector_separations")
        else run["sector_separations"]
    )
    return {
        "mode": name,
        "initial_separation": float(separations[0]),
        "final_separation": float(separations[-1]),
        "delta_separation": float(separations[-1] - separations[0]),
        "energy_drift": float(energies[-1] - energies[0]),
        "max_probability_error": float(
            max(
                np.max(np.abs(positive_probabilities - positive_probabilities[0])),
                np.max(np.abs(negative_probabilities - negative_probabilities[0])),
            )
        ),
    }


def build_payload(
    steps: int = 8,
    dt: float = 0.02,
    gravitational_constant: float = 0.05,
) -> dict[str, object]:
    state = initial_state()
    free = run_schrodinger_poisson_1d(state, steps=steps, dt=dt, gravitational_constant=0.0)
    janus = run_schrodinger_poisson_1d(
        state,
        steps=steps,
        dt=dt,
        gravitational_constant=gravitational_constant,
    )
    attractive = run_all_attractive_control(
        state,
        steps=steps,
        dt=dt,
        gravitational_constant=gravitational_constant,
    )
    rows = [
        summarize_run("free", free),
        summarize_run("janus_schrodinger_poisson", janus),
        summarize_run("all_attractive_control", attractive),
    ]
    checks = {
        "janus_separates": rows[1]["delta_separation"] > 0.0,
        "all_attractive_approaches": rows[2]["delta_separation"] < 0.0,
        "free_separation_stable": abs(rows[0]["delta_separation"]) < 1e-10,
        "probability_conserved": all(row["max_probability_error"] < 1e-12 for row in rows),
    }
    return {
        "settings": {
            "grid_n": 96,
            "box_half_width": 8.0,
            "steps": steps,
            "dt": dt,
            "gravitational_constant": gravitational_constant,
        },
        "rows": rows,
        "checks": checks,
        "passed": all(checks.values()),
        "boundary": (
            "Diagnostic only: 1D periodic frozen-potential quantum sandbox. "
            "Not a calibrated long-run solver or observational validation."
        ),
    }


def write_outputs(payload: dict[str, object]) -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = payload["rows"]

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write(
            "mode,initial_separation,final_separation,delta_separation,"
            "energy_drift,max_probability_error\n"
        )
        for row in rows:
            handle.write(
                f"{row['mode']},{row['initial_separation']:.12g},"
                f"{row['final_separation']:.12g},{row['delta_separation']:.12g},"
                f"{row['energy_drift']:.12g},{row['max_probability_error']:.12g}\n"
            )

    checks = payload["checks"]
    lines = [
        "# Quantum Janus 1D Diagnostic",
        "",
        "Short 1D comparison between free evolution, Janus Schrodinger-Poisson, and an all-attractive labelled control.",
        "",
        f"Passed: `{payload['passed']}`.",
        "",
        "## Settings",
        "",
    ]
    for key, value in payload["settings"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Results",
            "",
            "| mode | initial separation | final separation | delta separation | energy drift | max probability error |",
            "|---|---:|---:|---:|---:|---:|",
        ]
    )
    for row in rows:
        lines.append(
            f"| {row['mode']} | {row['initial_separation']:.6g} | "
            f"{row['final_separation']:.6g} | {row['delta_separation']:.6g} | "
            f"{row['energy_drift']:.6g} | {row['max_probability_error']:.3g} |"
        )
    lines.extend(["", "## Checks", ""])
    for key, value in checks.items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            payload["boundary"],
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    payload = build_payload()
    write_outputs(payload)
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
