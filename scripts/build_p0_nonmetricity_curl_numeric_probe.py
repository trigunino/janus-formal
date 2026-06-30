from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_nonmetricity_curl_numeric_probe.md")
JSON_PATH = Path("outputs/reports/p0_nonmetricity_curl_numeric_probe.json")
TOLERANCE = 1e-10


def periodic_derivative_2d(values: np.ndarray, axis: int, spacing: float) -> np.ndarray:
    return (np.roll(values, -1, axis=axis) - np.roll(values, 1, axis=axis)) / (2.0 * spacing)


def build_grid(n: int = 32, box_size: float = 2.0 * np.pi) -> tuple[np.ndarray, np.ndarray, float]:
    x = np.arange(n) * box_size / n
    y = np.arange(n) * box_size / n
    xx, yy = np.meshgrid(x, y, indexing="xy")
    return xx, yy, box_size / n


def build_scalar_h(xx: np.ndarray, yy: np.ndarray) -> np.ndarray:
    return np.sin(xx) * np.cos(yy) + 0.1 * np.cos(2.0 * xx + yy)


def build_matrix_h(xx: np.ndarray, yy: np.ndarray) -> np.ndarray:
    return np.stack(
        [
            np.stack(
                [
                    1.0 + 0.05 * np.sin(xx) + 0.02 * np.cos(yy),
                    0.03 * np.sin(xx + yy),
                ],
                axis=0,
            ),
            np.stack(
                [
                    0.02 * np.cos(2.0 * xx - yy),
                    1.0 - 0.04 * np.cos(xx) * np.sin(yy),
                ],
                axis=0,
            ),
        ],
        axis=0,
    )


def nonmetricity_from_h(h_field: np.ndarray, spacing: float) -> dict[str, np.ndarray]:
    return {
        "N_x": periodic_derivative_2d(h_field, axis=-1, spacing=spacing),
        "N_y": periodic_derivative_2d(h_field, axis=-2, spacing=spacing),
    }


def curl_residual(n_field: dict[str, np.ndarray], spacing: float) -> dict:
    curl = periodic_derivative_2d(n_field["N_y"], axis=-1, spacing=spacing) - periodic_derivative_2d(
        n_field["N_x"],
        axis=-2,
        spacing=spacing,
    )
    max_abs = float(np.max(np.abs(curl)))
    return {
        "max_abs_curl": max_abs,
        "rms_curl": float(np.sqrt(np.mean(curl**2))),
        "closed_at_tolerance": bool(max_abs < TOLERANCE),
    }


def inject_curl_defect(n_field: dict[str, np.ndarray], amount: float = 0.25) -> dict[str, np.ndarray]:
    defected = {name: values.copy() for name, values in n_field.items()}
    defect_index = (0,) * (defected["N_y"].ndim - 2) + (0, 0)
    defected["N_y"][defect_index] += amount
    return defected


def probe_h_case(name: str, h_field: np.ndarray, spacing: float) -> dict:
    n_field = nonmetricity_from_h(h_field, spacing)
    compatible = curl_residual(n_field, spacing)
    defected = curl_residual(inject_curl_defect(n_field), spacing)
    return {
        "name": name,
        "h_shape": [int(dim) for dim in h_field.shape],
        "compatible_curl": compatible,
        "curl_defected": defected,
        "compatible_curl_closes": compatible["closed_at_tolerance"],
        "curl_defected_closes": defected["closed_at_tolerance"],
    }


def build_payload() -> dict:
    xx, yy, spacing = build_grid()
    cases = [
        probe_h_case("scalar_H", build_scalar_h(xx, yy), spacing),
        probe_h_case("matrix_H_2x2", build_matrix_h(xx, yy), spacing),
    ]
    return {
        "description": "Numeric finite-difference probe for N_alpha=D_alpha H integrability on a bounded 2D grid.",
        "status": "nonmetricity-curl-numeric-probe-diagnostic",
        "depends_on": ["p0_nonmetricity_integrability_curl_gate"],
        "finite_difference_operator": "central periodic derivative",
        "grid_shape": [int(xx.shape[0]), int(xx.shape[1])],
        "spacing": float(spacing),
        "tolerance": TOLERANCE,
        "cases": cases,
        "all_compatible_curls_close": all(case["compatible_curl_closes"] for case in cases),
        "all_curl_defects_rejected": all(not case["curl_defected_closes"] for case in cases),
        "n_is_computed_as_dh": True,
        "scalar_and_matrix_h_supported": True,
        "uses_observational_fit": False,
        "uses_fitted_amplitude": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Componentwise finite differences close the curl residual when N is built as dH "
            "for scalar and matrix H. A pointwise curl defect fails, so this remains a "
            "diagnostic for the symbolic curl gate, not a fitted prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Nonmetricity Curl Numeric Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {', '.join(payload['depends_on'])}",
        f"Finite difference operator: {payload['finite_difference_operator']}",
        f"Grid shape: {payload['grid_shape']}",
        f"All compatible curls close: {payload['all_compatible_curls_close']}",
        f"All curl defects rejected: {payload['all_curl_defects_rejected']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses fitted amplitude: {payload['uses_fitted_amplitude']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Curl Rows",
        "",
        "| case | H shape | compatible max curl | defect max curl | defect closes |",
        "|---|---:|---:|---:|---|",
    ]
    for case in payload["cases"]:
        lines.append(
            f"| {case['name']} | {case['h_shape']} | "
            f"{case['compatible_curl']['max_abs_curl']:.12g} | "
            f"{case['curl_defected']['max_abs_curl']:.12g} | "
            f"{case['curl_defected_closes']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
