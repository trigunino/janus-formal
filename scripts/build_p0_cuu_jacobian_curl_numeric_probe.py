from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_cuu_jacobian_curl_numeric_probe.md")
JSON_PATH = Path("outputs/reports/p0_cuu_jacobian_curl_numeric_probe.json")
TOLERANCE = 1e-10


def periodic_derivative_2d(values: np.ndarray, axis: int, spacing: float) -> np.ndarray:
    return (np.roll(values, -1, axis=axis) - np.roll(values, 1, axis=axis)) / (2.0 * spacing)


def build_regular_patch(n: int = 32, box_size: float = 2.0 * np.pi) -> tuple[np.ndarray, float]:
    x = np.arange(n) * box_size / n
    y = np.arange(n) * box_size / n
    xx, yy = np.meshgrid(x, y, indexing="xy")
    phi_x = xx + 0.03 * np.sin(xx) * np.cos(yy)
    phi_y = yy + 0.02 * np.cos(xx) * np.sin(yy)
    return np.stack([phi_x, phi_y], axis=0), box_size / n


def jacobian_from_phi(phi: np.ndarray, spacing: float) -> np.ndarray:
    return np.stack(
        [
            [
                periodic_derivative_2d(phi[0], axis=1, spacing=spacing),
                periodic_derivative_2d(phi[0], axis=0, spacing=spacing),
            ],
            [
                periodic_derivative_2d(phi[1], axis=1, spacing=spacing),
                periodic_derivative_2d(phi[1], axis=0, spacing=spacing),
            ],
        ],
        axis=0,
    )


def jacobian_curl_residual(jacobian: np.ndarray, spacing: float) -> dict:
    rows = []
    for component in range(2):
        curl = (
            periodic_derivative_2d(jacobian[component, 1], axis=1, spacing=spacing)
            - periodic_derivative_2d(jacobian[component, 0], axis=0, spacing=spacing)
        )
        rows.append(
            {
                "component": f"phi_{component}",
                "max_abs_curl": float(np.max(np.abs(curl))),
                "rms_curl": float(np.sqrt(np.mean(curl**2))),
            }
        )
    max_abs = max(row["max_abs_curl"] for row in rows)
    return {
        "rows": rows,
        "max_abs_curl": max_abs,
        "closed_at_tolerance": bool(max_abs < TOLERANCE),
    }


def inject_curl_defect(jacobian: np.ndarray, amount: float = 0.25) -> np.ndarray:
    defected = jacobian.copy()
    defected[0, 1, 0, 0] += amount
    return defected


def build_payload() -> dict:
    phi, spacing = build_regular_patch()
    jacobian = jacobian_from_phi(phi, spacing)
    compatible = jacobian_curl_residual(jacobian, spacing)
    curl_defected = jacobian_curl_residual(inject_curl_defect(jacobian), spacing)
    return {
        "description": "Numeric curl probe for whether the candidate same-L Jacobian J can be a true dphi.",
        "status": "cuu-jacobian-curl-numeric-probe-diagnostic",
        "depends_on": [
            "p0_cuu_inverse_map_integrability_target",
            "p0_integrability_first_phi_l_selection",
        ],
        "grid_shape": [int(phi.shape[1]), int(phi.shape[2])],
        "spacing": float(spacing),
        "compatible_jacobian": compatible,
        "curl_defected_jacobian": curl_defected,
        "compatible_jacobian_curl_closes": compatible["closed_at_tolerance"],
        "curl_defected_jacobian_curl_closes": curl_defected["closed_at_tolerance"],
        "jacobian_is_from_phi_in_compatible_case": True,
        "defected_jacobian_is_pointwise_only": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A true dphi Jacobian passes the curl test, while a pointwise J with a local "
            "defect fails. This is a physical gate for Cuu mirror/integrability, not a closure proof."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Cuu Jacobian Curl Numeric Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Grid shape: {payload['grid_shape']}",
        f"Compatible Jacobian curl closes: {payload['compatible_jacobian_curl_closes']}",
        f"Curl-defected Jacobian curl closes: {payload['curl_defected_jacobian_curl_closes']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Curl Rows",
        "",
        "| case | component | max abs curl | rms curl |",
        "|---|---|---:|---:|",
    ]
    for case in ("compatible_jacobian", "curl_defected_jacobian"):
        for row in payload[case]["rows"]:
            lines.append(
                f"| {case} | {row['component']} | {row['max_abs_curl']:.12g} | "
                f"{row['rms_curl']:.12g} |"
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
