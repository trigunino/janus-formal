from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
import json

import numpy as np

from janus_lab.lensing import (
    janus_absolute_lensing_coefficients,
    janus_tensor_lensing_prefactor,
    standard_weak_lensing_prefactor,
)
from janus_lab.models import JanusExpansion
from janus_lab.physical_units import hubble_time_gyr, pm_hubble_velocity_unit_km_s


REPORT_PATH = Path("outputs/reports/pm_time_lensing_normalization_calibration.md")
JSON_PATH = Path("outputs/reports/pm_time_lensing_normalization_calibration.json")


def parse_float_list(text: str) -> np.ndarray:
    values = np.asarray([float(item.strip()) for item in text.split(",") if item.strip()])
    if values.size == 0:
        raise ValueError("list must not be empty.")
    return values


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--h0", type=float, default=70.0)
    parser.add_argument("--box-size-mpc", type=float, default=1000.0)
    parser.add_argument("--omega-abs", type=float, default=0.315)
    parser.add_argument("--q0", type=float, default=-0.087)
    parser.add_argument("--z-slices", type=int, default=64)
    parser.add_argument("--source-redshifts", default="0.8,1.2,1.6,2.0")
    parser.add_argument("--source-weights", default="")
    return parser.parse_args()


def build_payload(args) -> dict:
    source_redshifts = parse_float_list(args.source_redshifts)
    source_weights = (
        parse_float_list(args.source_weights)
        if args.source_weights.strip()
        else np.ones_like(source_redshifts)
    )
    if source_redshifts.shape != source_weights.shape:
        raise ValueError("source redshifts and weights must have the same length.")
    weights = source_weights / float(np.sum(source_weights))
    z_slices = np.linspace(0.0, float(np.max(source_redshifts)), args.z_slices)
    model = JanusExpansion.from_q0(args.q0)
    coefficients = janus_absolute_lensing_coefficients(
        z_slices,
        source_redshifts,
        weights,
        model,
        h0_km_s_mpc=args.h0,
        omega_abs=args.omega_abs,
    )
    base_prefactor = standard_weak_lensing_prefactor(args.h0, args.omega_abs)
    tensor_prefactor = janus_tensor_lensing_prefactor(
        args.h0,
        args.omega_abs,
        source_factor=1.0,
        determinant_ratio=1.0,
        cross_projection_ratio=1.0,
        projection_factor=1.0,
        distance_factor=1.0,
    )
    return {
        "description": "Working physical calibration for PM time and Janus lensing normalization.",
        "h0_km_s_mpc": args.h0,
        "box_size_mpc": args.box_size_mpc,
        "pm_time_unit_basis": "H0^-1",
        "pm_time_unit_gyr": hubble_time_gyr(args.h0),
        "pm_velocity_unit_km_s": pm_hubble_velocity_unit_km_s(
            args.box_size_mpc,
            args.h0,
        ),
        "omega_abs": args.omega_abs,
        "q0": args.q0,
        "source_redshifts": source_redshifts.tolist(),
        "source_weights_normalized": weights.tolist(),
        "base_prefactor": base_prefactor,
        "tensor_prefactor_unity_branch": tensor_prefactor,
        "tensor_normalization_formula": (
            "C_J=(3/2)*Omega_abs*(H0/c)^2*Q_source*Q_det*Q_cross*Q_proj*Q_dist"
        ),
        "working_branch": {
            "Q_source": 1.0,
            "Q_det": "1 under positive-effective negative-density convention",
            "Q_cross": "velocity-derived in PM source, equal-projection unity branch for coefficient audit",
            "Q_proj": "positive geodesic/Jacobi factor 1+z inside coefficients",
            "Q_dist": "M18 open comoving distance kernel inside coefficients",
        },
        "coefficient_sum": float(np.sum(coefficients)),
        "coefficient_max": float(np.max(coefficients)),
        "coefficient_argmax_z": float(z_slices[int(np.argmax(coefficients))]),
        "boundary": (
            "This closes the working calibration without fitting a scalar correction. "
            "It is still not a survey likelihood and does not prove the global tensor branch."
        ),
    }


def main() -> None:
    args = parse_args()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(args)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# PM Time And Lensing Normalization Calibration",
        "",
        payload["description"],
        "",
        "| item | value |",
        "|---|---:|",
        f"| H0 | {payload['h0_km_s_mpc']:.6g} km/s/Mpc |",
        f"| PM time unit | {payload['pm_time_unit_gyr']:.9g} Gyr |",
        f"| PM velocity unit | {payload['pm_velocity_unit_km_s']:.9g} km/s |",
        f"| base prefactor | {payload['base_prefactor']:.9g} |",
        f"| tensor unity-branch prefactor | {payload['tensor_prefactor_unity_branch']:.9g} |",
        f"| coefficient max | {payload['coefficient_max']:.9g} |",
        f"| coefficient peak z | {payload['coefficient_argmax_z']:.9g} |",
        "",
        "```text",
        payload["tensor_normalization_formula"],
        "```",
        "",
        payload["boundary"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
