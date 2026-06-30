from __future__ import annotations

from pathlib import Path
import json


ABSOLUTE_PATH = Path("outputs/reports/pm_qcross_absolute_shear.json")
RESOLUTION_PATH = Path("outputs/reports/pm_qcross_absolute_shear_resolution.json")
REPORT_PATH = Path("outputs/reports/observable_chain_consistency_audit.md")
JSON_PATH = Path("outputs/reports/observable_chain_consistency_audit.json")
MAX_ACCEPTABLE_RELATIVE_SHEAR_CHANGE = 1.0


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _csv(values) -> str:
    return ",".join(f"{float(value):.12g}" for value in values)


def _absolute_grid_summary(absolute: dict) -> dict:
    return {
        "grid": int(absolute["grid"]),
        "finite": bool(absolute["finite"]),
        "initial_state": absolute.get("initial_state", "unknown"),
        "seed": absolute.get("seed"),
        "shape_amplitude": absolute.get("shape_amplitude"),
        "displacement_scale": absolute.get("displacement_scale"),
        "shear_abs_rms": absolute.get("shear_abs_rms"),
        "first_shear_power": absolute.get("first_shear_power"),
        "generation_seconds": absolute.get("generation_seconds"),
    }


def _needed_resolution_command(absolute: dict, resolution: dict) -> str:
    grids = sorted({int(grid) for grid in resolution.get("grids", [])} | {int(absolute["grid"])})
    initial_state = str(absolute.get("initial_state", "bounded-gaussian_displacement_ic"))
    ic_family = initial_state.removesuffix("_displacement_ic")
    if ic_family == "bounded_anticorrelated_gaussian":
        ic_family = "bounded-gaussian"
    source_redshifts = absolute.get("source_redshifts", [0.8, 1.2, 1.6, 2.0])
    parts = [
        "python scripts/run_pm_qcross_absolute_shear_resolution.py",
        f"--grids {_csv(grids)}",
        f"--steps {absolute.get('steps', 4)}",
        "--dt 0.0001",
        "--gravity-scale 0.5",
        "--box-size-mpc 1000",
        f"--h0 {float(absolute.get('h0_km_s_mpc', 70.0)):.12g}",
        f"--omega-abs {float(absolute.get('omega_abs', 0.315)):.12g}",
        "--q0 -0.087",
        f"--source-redshifts {_csv(source_redshifts)}",
    ]
    if absolute.get("source_weights_normalized"):
        parts.append(f"--source-weights {_csv(absolute['source_weights_normalized'])}")
    parts.extend(
        [
            "--axis 2",
            f"--seed {absolute.get('seed', 20260621)}",
            f"--shape-amplitude {float(absolute.get('shape_amplitude', 1.0)):.12g}",
            f"--displacement-scale {float(absolute.get('displacement_scale', 0.05)):.12g}",
            f"--ic-family {ic_family}",
        ]
    )
    return " ".join(parts)


def build_payload(
    absolute_path: Path = ABSOLUTE_PATH,
    resolution_path: Path = RESOLUTION_PATH,
) -> dict:
    absolute = load_json(absolute_path)
    resolution = load_json(resolution_path)
    absolute_grid = int(absolute["grid"])
    resolution_max_grid = int(resolution["max_grid"])
    required_grid = int(resolution["required_grid_for_sigma8_radius"])
    max_relative_shear_change = resolution.get("max_relative_shear_change")
    amplitude_resolution_stable = (
        max_relative_shear_change is not None
        and float(max_relative_shear_change) <= MAX_ACCEPTABLE_RELATIVE_SHEAR_CHANGE
    )
    checks = {
        "absolute_run_reaches_required_grid": absolute_grid >= required_grid,
        "resolution_report_reaches_required_grid": resolution_max_grid >= required_grid,
        "resolution_report_covers_absolute_grid": resolution_max_grid >= absolute_grid,
        "absolute_run_finite": bool(absolute["finite"]),
        "resolution_runs_finite": bool(resolution["finite"]),
        "amplitude_resolution_stable": amplitude_resolution_stable,
    }
    blockers = []
    if not checks["absolute_run_reaches_required_grid"]:
        blockers.append("absolute run does not reach the required sigma8 grid")
    if not checks["resolution_report_reaches_required_grid"]:
        blockers.append("resolution report does not include the required sigma8 grid")
    if not checks["resolution_report_covers_absolute_grid"]:
        blockers.append("resolution report does not cover the existing absolute run grid")
    if not checks["absolute_run_finite"]:
        blockers.append("absolute run is not finite")
    if not checks["resolution_runs_finite"]:
        blockers.append("one or more resolution runs are not finite")
    if not checks["amplitude_resolution_stable"]:
        blockers.append("absolute shear amplitude is not resolution-stable")
    blocking_issue = bool(blockers)
    return {
        "description": "Consistency audit for the PM Q_cross absolute observable chain.",
        "absolute_grid": absolute_grid,
        "existing_absolute_run": _absolute_grid_summary(absolute),
        "resolution_max_grid": resolution_max_grid,
        "required_grid": required_grid,
        "max_relative_shear_change": max_relative_shear_change,
        "max_acceptable_relative_shear_change": MAX_ACCEPTABLE_RELATIVE_SHEAR_CHANGE,
        "checks": checks,
        "blocking_issue": blocking_issue,
        "blockers": blockers,
        "needed_data": (
            "A single resolution report generated by "
            "scripts/run_pm_qcross_absolute_shear_resolution.py with the 175^3 row "
            "computed under the same settings as the lower-grid rows. The existing "
            "standalone 175^3 absolute run is recorded here but is not enough by "
            "itself to close convergence."
        ),
        "needed_command": _needed_resolution_command(absolute, resolution),
        "verdict": (
            "Existing 175^3 absolute output is finite, but convergence is not closed "
            "until the resolution report covers the grid and the absolute shear amplitude "
            "is resolution-stable."
            if blocking_issue
            else "Absolute output is grid-covered and amplitude-stable under this diagnostic."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Observable Chain Consistency Audit",
        "",
        payload["description"],
        "",
        f"- absolute grid: {payload['absolute_grid']}",
        f"- resolution max grid: {payload['resolution_max_grid']}",
        f"- required grid: {payload['required_grid']}",
        f"- max relative shear change: {payload['max_relative_shear_change']}",
        f"- max acceptable relative shear change: {payload['max_acceptable_relative_shear_change']}",
        f"- existing 175^3 shear RMS: {payload['existing_absolute_run']['shear_abs_rms']}",
        f"- existing 175^3 finite: {payload['existing_absolute_run']['finite']}",
        "",
        "| check | value |",
        "|---|---|",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"| {key} | {value} |")
    lines.extend(
        [
            "",
            f"Verdict: {payload['verdict']}",
            "",
            "Blockers:",
        ]
    )
    if payload["blockers"]:
        lines.extend(f"- {blocker}" for blocker in payload["blockers"])
    else:
        lines.append("- none")
    lines.extend(
        [
            "",
            "Needed data:",
            payload["needed_data"],
            "",
            "Needed command:",
            f"`{payload['needed_command']}`",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
