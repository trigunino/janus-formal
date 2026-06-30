from __future__ import annotations

from pathlib import Path
import json

import numpy as np
from scipy import linalg


REPORT_PATH = Path("outputs/reports/p0_bianchi_minimal_curvature_numeric_probe.md")
JSON_PATH = Path("outputs/reports/p0_bianchi_minimal_curvature_numeric_probe.json")


def solve_linear_probe(matrix: np.ndarray, rhs: np.ndarray) -> dict:
    solution, residuals, rank, singular_values = linalg.lstsq(matrix, rhs)
    residual = matrix @ solution - rhs
    return {
        "rank": int(rank),
        "unknown_count": int(matrix.shape[1]),
        "equation_count": int(matrix.shape[0]),
        "solution": [float(value) for value in solution],
        "residual_norm": float(linalg.norm(residual)),
        "singular_values": [float(value) for value in singular_values],
        "closed_at_tolerance": bool(linalg.norm(residual) < 1e-10),
    }


def flrw_relative_curvature_rhs(
    h_plus: float,
    h_minus: float,
    dh_plus: float,
    dh_minus: float,
) -> np.ndarray:
    f_i0 = (dh_minus + h_minus**2) - (dh_plus + h_plus**2)
    f_ij = h_minus**2 - h_plus**2
    return np.array([f_i0, f_i0, f_ij, f_ij], dtype=float)


def build_payload() -> dict:
    # Linearized local model:
    # x=(A_perp_1, A_perp_2, R_1, R_2). Rows are toy curvature components.
    probe_matrix = np.array(
        [
            [1.0, 0.0, 1.0, 0.0],
            [0.0, 1.0, 0.0, -1.0],
            [1.0, 1.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 1.0],
        ]
    )
    compatible_rhs = np.array([1.0, -1.0, 0.5, 0.25])
    incompatible_matrix = np.vstack([probe_matrix, np.array([[1.0, 1.0, 0.0, 0.0]])])
    incompatible_rhs = np.array([1.0, -1.0, 0.5, 0.25, 1.5])

    compatible = solve_linear_probe(probe_matrix, compatible_rhs)
    incompatible = solve_linear_probe(incompatible_matrix, incompatible_rhs)
    flrw_rhs = flrw_relative_curvature_rhs(
        h_plus=0.72,
        h_minus=0.70,
        dh_plus=-0.10,
        dh_minus=-0.08,
    )
    flrw_probe = solve_linear_probe(probe_matrix, flrw_rhs)

    return {
        "description": (
            "Numerical scipy probe for the linearized curvature-integrability closure test. "
            "It exercises the algebraic solver path for A_perp_i/R_alpha without fitting data."
        ),
        "status": "numeric-probe-only",
        "depends_on": "p0_bianchi_minimal_curvature_integrability_system",
        "tooling": ["numpy", "scipy.linalg.lstsq"],
        "unknown_vector": ["A_perp_1", "A_perp_2", "R_1", "R_2"],
        "compatible_probe": compatible,
        "incompatible_probe": incompatible,
        "flrw_source_probe": flrw_probe,
        "flrw_source_rhs": [float(value) for value in flrw_rhs],
        "probe_matrix_shape": list(probe_matrix.shape),
        "incompatible_matrix_shape": list(incompatible_matrix.shape),
        "compatible_case_closes": compatible["closed_at_tolerance"],
        "incompatible_case_closes": incompatible["closed_at_tolerance"],
        "flrw_source_case_closes": flrw_probe["closed_at_tolerance"],
        "uses_observational_fit": False,
        "uses_posthoc_qcross": False,
        "source_curvature_data_supplied": "homogeneous-flrw-symbolic-proxy",
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The scipy path is ready: given source-computable relative curvature rows, "
            "the code can distinguish solvable from incompatible A_perp/R systems. "
            "A homogeneous FLRW symbolic proxy is included, but this is not full physics "
            "closure because perturbative Janus F_relative rows are not supplied here."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Bianchi-Minimal Curvature Numeric Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Tooling: {', '.join(payload['tooling'])}",
        f"Unknown vector: {payload['unknown_vector']}",
        f"Compatible case closes: {payload['compatible_case_closes']}",
        f"Incompatible case closes: {payload['incompatible_case_closes']}",
        f"FLRW source case closes: {payload['flrw_source_case_closes']}",
        f"FLRW source RHS: {payload['flrw_source_rhs']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses posthoc Q_cross: {payload['uses_posthoc_qcross']}",
        f"Source curvature data supplied: {payload['source_curvature_data_supplied']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Probe Results",
        "",
        "| case | equations | unknowns | rank | residual norm | closes |",
        "|---|---|---|---|---|---|",
    ]
    for name in ("compatible_probe", "incompatible_probe", "flrw_source_probe"):
        row = payload[name]
        lines.append(
            f"| {name} | {row['equation_count']} | {row['unknown_count']} | "
            f"{row['rank']} | {row['residual_norm']:.12g} | {row['closed_at_tolerance']} |"
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
