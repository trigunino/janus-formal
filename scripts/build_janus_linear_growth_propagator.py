from __future__ import annotations

from argparse import ArgumentParser, Namespace
from pathlib import Path
import json

import numpy as np

from janus_lab.models import JanusExpansion


REPORT_PATH = Path("outputs/reports/janus_linear_growth_propagator.md")
JSON_PATH = Path("outputs/reports/janus_linear_growth_propagator.json")


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--q0", type=float, default=-0.087)
    parser.add_argument("--a-initial", type=float, default=0.2)
    parser.add_argument("--a-final", type=float, default=1.0)
    parser.add_argument("--samples", type=int, default=64)
    parser.add_argument("--omega-plus", type=float, default=0.5)
    parser.add_argument("--omega-minus", type=float, default=0.5)
    return parser.parse_args()


def e_of_a(model: JanusExpansion, scale_factor: float) -> float:
    if scale_factor <= 0.0:
        raise ValueError("scale factor must be positive.")
    return float(model.e(1.0 / scale_factor - 1.0))


def dlnh_dlna(model: JanusExpansion, scale_factor: float, step: float = 1e-4) -> float:
    ln_a = np.log(scale_factor)
    a_min = 1.0 / (1.0 + model.z_max)
    a_left = float(np.exp(ln_a - step))
    a_right = float(np.exp(ln_a + step))
    if a_right > 1.0:
        a_left = float(np.exp(ln_a - step))
        return float((np.log(e_of_a(model, scale_factor)) - np.log(e_of_a(model, a_left))) / step)
    if a_left < a_min:
        a_right = float(np.exp(ln_a + step))
        return float((np.log(e_of_a(model, a_right)) - np.log(e_of_a(model, scale_factor))) / step)
    return float((np.log(e_of_a(model, a_right)) - np.log(e_of_a(model, a_left))) / (2.0 * step))


def friction_a(model: JanusExpansion, scale_factor: float) -> float:
    return 2.0 + dlnh_dlna(model, scale_factor)


def integrate_mode(
    model: JanusExpansion,
    *,
    a_initial: float,
    a_final: float,
    samples: int,
    eigenvalue: float,
    initial_value: float = 1.0,
    initial_derivative: float = 0.0,
) -> dict:
    if a_initial <= 0.0 or a_final <= a_initial:
        raise ValueError("require 0 < a_initial < a_final.")
    if a_final > 1.0:
        raise ValueError("a_final must not exceed 1 for this Janus expansion branch.")
    if a_initial < 1.0 / (1.0 + model.z_max):
        raise ValueError("a_initial is below this Janus model's z_max support.")
    if samples < 2:
        raise ValueError("samples must be at least two.")

    x_values = np.linspace(np.log(a_initial), np.log(a_final), samples)
    y = np.asarray([initial_value, initial_derivative], dtype=float)
    rows = []

    def rhs(x: float, state: np.ndarray) -> np.ndarray:
        a = float(np.exp(x))
        d, dp = state
        return np.asarray([dp, eigenvalue * d - friction_a(model, a) * dp], dtype=float)

    for index, x in enumerate(x_values):
        a = float(np.exp(x))
        rows.append(
            {
                "a": a,
                "value": float(y[0]),
                "d_dln_a": float(y[1]),
                "E_J": e_of_a(model, a),
                "A_drag": friction_a(model, a),
            }
        )
        if index == len(x_values) - 1:
            break
        h = float(x_values[index + 1] - x)
        k1 = rhs(float(x), y)
        k2 = rhs(float(x + 0.5 * h), y + 0.5 * h * k1)
        k3 = rhs(float(x + 0.5 * h), y + 0.5 * h * k2)
        k4 = rhs(float(x + h), y + h * k3)
        y = y + h * (k1 + 2.0 * k2 + 2.0 * k3 + k4) / 6.0

    return {
        "initial_value": initial_value,
        "initial_derivative": initial_derivative,
        "final_value": rows[-1]["value"],
        "final_d_dln_a": rows[-1]["d_dln_a"],
        "rows": rows,
    }


def build_payload(args: Namespace) -> dict:
    model = JanusExpansion.from_q0(args.q0)
    omega_plus = float(args.omega_plus)
    omega_minus = float(args.omega_minus)
    if omega_plus < 0.0 or omega_minus < 0.0:
        raise ValueError("omega inputs must be non-negative.")
    lambda_null = 0.0
    lambda_source = 1.5 * (omega_plus + omega_minus)
    null_mode = integrate_mode(
        model,
        a_initial=args.a_initial,
        a_final=args.a_final,
        samples=args.samples,
        eigenvalue=lambda_null,
    )
    source_mode = integrate_mode(
        model,
        a_initial=args.a_initial,
        a_final=args.a_final,
        samples=args.samples,
        eigenvalue=lambda_source,
    )
    return {
        "description": "Diagnostic propagator for weak-field Janus linear growth modes.",
        "q0": args.q0,
        "a_initial": args.a_initial,
        "a_final": args.a_final,
        "samples": args.samples,
        "omega_inputs": {
            "omega_plus": omega_plus,
            "omega_minus": omega_minus,
            "status": "declared diagnostic inputs, not fitted observables",
        },
        "eigenvalues": {
            "null": lambda_null,
            "source": lambda_source,
        },
        "modes": {
            "null": null_mode,
            "source": source_mode,
        },
        "physics_closed": False,
        "amplitude_normalized": False,
        "verdict": (
            "The propagator is a no-fit weak-field diagnostic for declared Omega inputs. "
            "It does not derive T_J(k), A_J, or production initial conditions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear Growth Propagator",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        f"Amplitude normalized: {payload['amplitude_normalized']}",
        "",
        "| mode | eigenvalue | final value | final d/dln a |",
        "|---|---:|---:|---:|",
    ]
    for name in ("null", "source"):
        mode = payload["modes"][name]
        lines.append(
            f"| {name} | {payload['eigenvalues'][name]:.9g} | "
            f"{mode['final_value']:.9g} | {mode['final_d_dln_a']:.9g} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(parse_args())
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
