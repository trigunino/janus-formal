from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_same_l_qcross_numeric_contraction_probe.md")
JSON_PATH = Path("outputs/reports/p0_same_l_qcross_numeric_contraction_probe.json")
ETA = np.diag([-1.0, 1.0, 1.0, 1.0])
TOLERANCE = 1e-12


def lorentz_like_boost(beta: float) -> np.ndarray:
    gamma = 1.0 / np.sqrt(1.0 - beta**2)
    return np.array(
        [
            [gamma, beta * gamma, 0.0, 0.0],
            [beta * gamma, gamma, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0],
            [0.0, 0.0, 0.0, 1.0],
        ],
        dtype=float,
    )


def metric_preservation_error(transform: np.ndarray) -> float:
    return float(np.max(np.abs(transform.T @ ETA @ transform - ETA)))


def null_error(covector: np.ndarray) -> float:
    return float(covector @ ETA @ covector)


def qcross_from_k_contraction(
    transform: np.ndarray,
    covector: np.ndarray,
    source_velocity: np.ndarray,
    density: float = 1.0,
) -> tuple[float, float]:
    transported_velocity = transform @ source_velocity
    k_contraction = density * float(covector @ transported_velocity) ** 2
    source_contraction = density * float(covector @ source_velocity) ** 2
    return k_contraction, k_contraction / source_contraction


def build_probe_rows(
    k_transform: np.ndarray,
    optical_transform: np.ndarray,
    covectors: dict[str, np.ndarray],
    source_velocity: np.ndarray,
) -> list[dict]:
    rows = []
    for name, covector in covectors.items():
        k_contraction, geometric_qcross = qcross_from_k_contraction(
            k_transform, covector, source_velocity
        )
        _, same_l_optical_qcross = qcross_from_k_contraction(
            k_transform, covector, source_velocity
        )
        _, independent_optical_qcross = qcross_from_k_contraction(
            optical_transform, covector, source_velocity
        )
        rows.append(
            {
                "covector": name,
                "null_error": null_error(covector),
                "k_contraction": k_contraction,
                "geometric_qcross": geometric_qcross,
                "same_l_optical_qcross": same_l_optical_qcross,
                "same_l_residual": abs(geometric_qcross - same_l_optical_qcross),
                "independent_optical_qcross": independent_optical_qcross,
                "independent_l_residual": abs(
                    geometric_qcross - independent_optical_qcross
                ),
            }
        )
    return rows


def build_payload() -> dict:
    source_velocity = np.array([1.0, 0.0, 0.0, 0.0])
    k_transform = lorentz_like_boost(beta=0.30)
    independent_optical_transform = lorentz_like_boost(beta=0.18)
    covectors = {
        "forward_x": np.array([1.0, 1.0, 0.0, 0.0]),
        "transverse_y": np.array([1.0, 0.0, 1.0, 0.0]),
        "backward_x": np.array([1.0, -1.0, 0.0, 0.0]),
    }
    rows = build_probe_rows(
        k_transform,
        independent_optical_transform,
        covectors,
        source_velocity,
    )
    same_l_max_residual = max(row["same_l_residual"] for row in rows)
    independent_l_min_residual = min(row["independent_l_residual"] for row in rows)

    return {
        "description": (
            "Bounded P0 numeric artifact for same-L Q_cross contraction consistency. "
            "The toy K contraction and geometric Q_cross use the same Lorentz-like L."
        ),
        "status": "numeric-artifact-only",
        "depends_on": "bianchi_lorentz_boost_transport_branch",
        "tooling": ["numpy"],
        "metric_signature": "eta_AB=diag(-1,1,1,1)",
        "k_lorentz_beta": 0.30,
        "independent_optical_l_beta": 0.18,
        "k_lorentz_error": metric_preservation_error(k_transform),
        "independent_optical_l_error": metric_preservation_error(
            independent_optical_transform
        ),
        "covectors": list(covectors),
        "probe_rows": rows,
        "same_l_max_residual": same_l_max_residual,
        "same_l_consistent": same_l_max_residual < TOLERANCE,
        "independent_l_min_residual": independent_l_min_residual,
        "independent_optical_l_shortcut_allowed": False,
        "uses_observational_fit": False,
        "uses_posthoc_qcross": False,
        "uses_posthoc_scalar_absorption": False,
        "uses_qdet_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "forbidden_shortcuts": [
            "independent optical-L shortcut not induced by the same L used for K contraction",
            "posthoc scalar Q_cross absorption",
            "Qdet absorption of the contraction residual",
            "observational fit or fitted normalization",
        ],
        "verdict": (
            "Same-L contractions agree in the toy numeric probe. An independently chosen "
            "optical L gives different Q_cross values and remains forbidden."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Same-L Q_cross Numeric Contraction Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Tooling: {', '.join(payload['tooling'])}",
        f"Metric signature: {payload['metric_signature']}",
        f"K Lorentz beta: {payload['k_lorentz_beta']}",
        f"Independent optical-L beta: {payload['independent_optical_l_beta']}",
        f"Same-L consistent: {payload['same_l_consistent']}",
        f"Independent optical-L shortcut allowed: {payload['independent_optical_l_shortcut_allowed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses posthoc Q_cross: {payload['uses_posthoc_qcross']}",
        f"Uses posthoc scalar absorption: {payload['uses_posthoc_scalar_absorption']}",
        f"Uses Qdet absorption: {payload['uses_qdet_absorption']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Probe Rows",
        "",
        "| covector | null error | K contraction | geometric Q_cross | same-L residual | independent-L residual |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for row in payload["probe_rows"]:
        lines.append(
            f"| {row['covector']} | {row['null_error']:.3g} | "
            f"{row['k_contraction']:.12g} | {row['geometric_qcross']:.12g} | "
            f"{row['same_l_residual']:.3g} | {row['independent_l_residual']:.12g} |"
        )
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
