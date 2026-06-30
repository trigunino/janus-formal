from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import json

from janus_lab.physical_units import (
    PhysicalBoxCalibration,
    hubble_time_gyr,
    pm_hubble_velocity_unit_km_s,
)


REPORT_PATH = Path("outputs/reports/janus_ic_source_targets.md")
JSON_PATH = Path("outputs/reports/janus_ic_source_targets.json")


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--h0", type=float, default=70.0)
    parser.add_argument("--box-size-mpc", type=float, default=1000.0)
    parser.add_argument("--omega-abs", type=float, default=0.315)
    parser.add_argument("--grid", type=int, default=8)
    return parser.parse_args()


def build_payload(args) -> dict:
    calibration = PhysicalBoxCalibration.from_total_absolute_omega(
        box_size_mpc=args.box_size_mpc,
        grid_shape=(args.grid, args.grid, args.grid),
        h0_km_s_mpc=args.h0,
        omega_abs=args.omega_abs,
        positive_fraction=0.5,
    )
    keeper_calibrations = [
        {
            "item": "PM time unit",
            "status": "keeper_working_calibration",
            "basis": "dimensionless PM equations use E(a)=H/H0",
            "value": "H0^-1",
            "numeric_value": hubble_time_gyr(args.h0),
            "unit": "Gyr",
            "rule": "Keep unless full Janus PM equations derive a different code time variable.",
        },
        {
            "item": "PM velocity unit",
            "status": "keeper_working_calibration",
            "basis": "box length divided by H0^-1",
            "value": "H0 * box_size",
            "numeric_value": pm_hubble_velocity_unit_km_s(args.box_size_mpc, args.h0),
            "unit": "km/s",
            "rule": "Converts PM velocities only; it is not a source-derived velocity field.",
        },
        {
            "item": "sigma8 resolution gate",
            "status": "keeper_numerical_gate",
            "basis": "physical box calibration",
            "value": "minimum grid for 8 h^-1 Mpc radius",
            "numeric_value": calibration.grid_n_required_for_radius(
                calibration.sigma8_radius_mpc
            ),
            "unit": "cells per axis",
            "rule": "Resolution bookkeeping only; it cannot replace transfer or amplitude physics.",
        },
    ]
    missing_source_targets = [
        {
            "target": "transfer",
            "symbol": "T_J(k,a)",
            "status": "missing_source_derivation",
            "required_piece": "Janus two-sector positive-density transfer function.",
            "forbidden_substitute": "Gaussian spectral index, cutoff, lognormal transform, or bounded tanh field.",
            "blocks_final_ic": True,
        },
        {
            "target": "growth",
            "symbol": "D_+(k,a), D_-(k,a)",
            "status": "missing_source_derivation",
            "required_piece": "Growth law tied to Janus expansion and sector coupling.",
            "forbidden_substitute": "PM growth ratios from toy seeds or convergence diagnostics.",
            "blocks_final_ic": True,
        },
        {
            "target": "amplitude",
            "symbol": "A_J or source-backed sigma8/S8 map",
            "status": "missing_source_derivation",
            "required_piece": "Non-fit normalization rule from sources or an explicit no-fit comparison target.",
            "forbidden_substitute": "Rescaling a toy field to sigma8=0.8.",
            "blocks_final_ic": True,
        },
        {
            "target": "velocity",
            "symbol": "v_+(k,a), v_-(k,a)",
            "status": "missing_source_derivation",
            "required_piece": "Continuity/growth-derived sector velocity fields compatible with T_J and D_J.",
            "forbidden_substitute": "Demo velocity patterns or arbitrary displacement-scale tuning.",
            "blocks_final_ic": True,
        },
    ]
    return {
        "description": (
            "Initial-condition scaffold boundary: keep PM time calibration separate from "
            "missing Janus source-derived transfer/growth/amplitude/velocity targets."
        ),
        "h0_km_s_mpc": args.h0,
        "box_size_mpc": args.box_size_mpc,
        "omega_abs": args.omega_abs,
        "grid": args.grid,
        "sigma8_radius_mpc": calibration.sigma8_radius_mpc,
        "current_resolves_sigma8": calibration.resolves_radius(calibration.sigma8_radius_mpc),
        "artificial_fits_allowed": False,
        "keeper_calibrations": keeper_calibrations,
        "missing_source_targets": missing_source_targets,
        "verdict": (
            "The H0^-1 PM time layer is keepable calibration. The IC transfer, growth, "
            "amplitude, and velocity pieces remain source-derived blockers; toy IC families "
            "stay diagnostics only."
        ),
    }


def main() -> None:
    args = parse_args()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(args)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Janus IC Source Targets",
        "",
        payload["description"],
        "",
        "| keeper calibration | status | value | rule |",
        "|---|---|---:|---|",
    ]
    for item in payload["keeper_calibrations"]:
        lines.append(
            f"| {item['item']} | {item['status']} | "
            f"{item['numeric_value']:.9g} {item['unit']} | {item['rule']} |"
        )
    lines.extend(
        [
            "",
            "| missing target | symbol | required source piece | forbidden substitute |",
            "|---|---|---|---|",
        ]
    )
    for item in payload["missing_source_targets"]:
        lines.append(
            f"| {item['target']} | `{item['symbol']}` | {item['required_piece']} | "
            f"{item['forbidden_substitute']} |"
        )
    lines.extend(
        [
            "",
            f"Artificial fits allowed: `{payload['artificial_fits_allowed']}`.",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
