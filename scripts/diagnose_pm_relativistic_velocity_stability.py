from __future__ import annotations

from argparse import ArgumentParser, Namespace
from pathlib import Path
import json

try:
    from scripts.run_pm_qcross_absolute_shear import build_payload as build_absolute_shear_payload
except ModuleNotFoundError:
    from run_pm_qcross_absolute_shear import build_payload as build_absolute_shear_payload


REPORT_PATH = Path("outputs/reports/pm_relativistic_velocity_stability.md")
JSON_PATH = Path("outputs/reports/pm_relativistic_velocity_stability.json")


def parse_int_list(text: str) -> list[int]:
    values = [int(item.strip()) for item in text.split(",") if item.strip()]
    if not values:
        raise ValueError("integer list must not be empty.")
    return values


def parse_float_list(text: str) -> list[float]:
    values = [float(item.strip()) for item in text.split(",") if item.strip()]
    if not values:
        raise ValueError("float list must not be empty.")
    return values


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--grids", default="96,128")
    parser.add_argument("--displacement-scales", default="0.005,0.001")
    parser.add_argument("--steps", type=int, default=4)
    parser.add_argument("--dt", type=float, default=0.0001)
    parser.add_argument("--gravity-scale", type=float, default=0.5)
    parser.add_argument("--box-size-mpc", type=float, default=1000.0)
    parser.add_argument("--h0", type=float, default=70.0)
    parser.add_argument("--omega-abs", type=float, default=0.315)
    parser.add_argument("--q0", type=float, default=-0.087)
    parser.add_argument("--source-redshifts", default="0.8,1.2,1.6,2.0")
    parser.add_argument("--source-weights", default="")
    parser.add_argument("--axis", type=int, default=2)
    parser.add_argument("--seed", type=int, default=20260621)
    parser.add_argument("--shape-amplitude", type=float, default=1.0)
    parser.add_argument(
        "--ic-family",
        choices=("bounded-gaussian", "analytic-multimode"),
        default="bounded-gaussian",
    )
    return parser.parse_args()


def build_payload(args) -> dict:
    rows = []
    for grid in parse_int_list(args.grids):
        for displacement_scale in parse_float_list(args.displacement_scales):
            row = {
                "grid": grid,
                "displacement_scale": displacement_scale,
                "valid": False,
                "error": "",
                "speed_max_km_s": None,
                "shear_abs_rms": None,
                "generation_seconds": None,
            }
            try:
                payload = build_absolute_shear_payload(
                    Namespace(
                        grid=grid,
                        steps=args.steps,
                        dt=args.dt,
                        gravity_scale=args.gravity_scale,
                        box_size_mpc=args.box_size_mpc,
                        h0=args.h0,
                        omega_abs=args.omega_abs,
                        q0=args.q0,
                        source_redshifts=args.source_redshifts,
                        source_weights=args.source_weights,
                        axis=args.axis,
                        seed=args.seed,
                        shape_amplitude=args.shape_amplitude,
                        displacement_scale=displacement_scale,
                        ic_family=args.ic_family,
                    )
                )
                row.update(
                    {
                        "valid": bool(payload["finite"]),
                        "speed_max_km_s": payload["source_metrics"]["speed_max_km_s"],
                        "shear_abs_rms": payload["shear_abs_rms"],
                        "generation_seconds": payload["generation_seconds"],
                    }
                )
            except ValueError as exc:
                row["error"] = str(exc)
            rows.append(row)
    return {
        "description": "Relativistic velocity stability scan for PM Q_cross diagnostics.",
        "rows": rows,
        "valid_count": sum(1 for row in rows if row["valid"]),
        "invalid_count": sum(1 for row in rows if not row["valid"]),
        "boundary": (
            "Numerical admissibility scan only. Smaller displacement scales are stability "
            "settings for the prototype IC, not observational fits."
        ),
    }


def main() -> None:
    args = parse_args()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(args)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# PM Relativistic Velocity Stability",
        "",
        payload["description"],
        "",
        "| grid | displacement scale | valid | speed max km/s | shear RMS | error | seconds |",
        "|---:|---:|---|---:|---:|---|---:|",
    ]
    for row in payload["rows"]:
        speed = "" if row["speed_max_km_s"] is None else f"{row['speed_max_km_s']:.9g}"
        shear = "" if row["shear_abs_rms"] is None else f"{row['shear_abs_rms']:.9g}"
        seconds = "" if row["generation_seconds"] is None else f"{row['generation_seconds']:.6g}"
        lines.append(
            f"| {row['grid']} | {row['displacement_scale']:.6g} | {row['valid']} | "
            f"{speed} | {shear} | {row['error']} | {seconds} |"
        )
    lines.extend(["", payload["boundary"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
