from __future__ import annotations

from pathlib import Path
import json

import numpy as np
from scipy import sparse
from scipy.sparse import linalg as sparse_linalg


REPORT_PATH = Path("outputs/reports/p0_curvature_integrability_sparse_pde_probe.md")
JSON_PATH = Path("outputs/reports/p0_curvature_integrability_sparse_pde_probe.json")


def build_gradient_system(nx: int, ny: int, potential: np.ndarray, defect: float = 0.0) -> tuple[sparse.csr_matrix, np.ndarray]:
    rows: list[tuple[int, int, float]] = []
    rhs: list[float] = []
    row = 0

    def idx(x: int, y: int) -> int:
        return y * nx + x

    for y in range(ny):
        for x in range(nx - 1):
            rows.append((row, idx(x + 1, y), 1.0))
            rows.append((row, idx(x, y), -1.0))
            rhs.append(float(potential[y, x + 1] - potential[y, x]))
            row += 1
    for y in range(ny - 1):
        for x in range(nx):
            rows.append((row, idx(x, y + 1), 1.0))
            rows.append((row, idx(x, y), -1.0))
            value = float(potential[y + 1, x] - potential[y, x])
            if x == 0 and y == 0:
                value += defect
            rhs.append(value)
            row += 1

    # Gauge fix: one potential value is anchored, not fitted.
    rows.append((row, 0, 1.0))
    rhs.append(float(potential[0, 0]))

    matrix = sparse.coo_matrix(
        ([value for _, _, value in rows], ([r for r, _, _ in rows], [c for _, c, _ in rows])),
        shape=(row + 1, nx * ny),
    ).tocsr()
    return matrix, np.array(rhs, dtype=float)


def discrete_curl_defects(nx: int, ny: int, rhs: np.ndarray) -> np.ndarray:
    horizontal_count = ny * (nx - 1)
    vertical_count = (ny - 1) * nx
    horizontal = rhs[:horizontal_count].reshape(ny, nx - 1)
    vertical = rhs[horizontal_count : horizontal_count + vertical_count].reshape(ny - 1, nx)
    defects: list[float] = []
    for y in range(ny - 1):
        for x in range(nx - 1):
            loop_sum = horizontal[y, x] + vertical[y, x + 1] - horizontal[y + 1, x] - vertical[y, x]
            defects.append(float(loop_sum))
    return np.array(defects, dtype=float)


def solve_sparse_probe(matrix: sparse.csr_matrix, rhs: np.ndarray) -> dict:
    result = sparse_linalg.lsqr(matrix, rhs, atol=1e-12, btol=1e-12)
    solution = result[0]
    residual = matrix @ solution - rhs
    residual_norm = float(np.linalg.norm(residual))
    return {
        "equation_count": int(matrix.shape[0]),
        "unknown_count": int(matrix.shape[1]),
        "iterations": int(result[2]),
        "residual_norm": residual_norm,
        "closed_at_tolerance": bool(residual_norm < 1e-10),
        "solution_norm": float(np.linalg.norm(solution)),
    }


def build_payload() -> dict:
    potential = np.array(
        [
            [0.0, 0.2, 0.5],
            [0.1, 0.4, 0.9],
            [0.3, 0.8, 1.4],
        ],
        dtype=float,
    )
    compatible_matrix, compatible_rhs = build_gradient_system(3, 3, potential)
    incompatible_matrix, incompatible_rhs = build_gradient_system(3, 3, potential, defect=0.25)
    compatible = solve_sparse_probe(compatible_matrix, compatible_rhs)
    incompatible = solve_sparse_probe(incompatible_matrix, incompatible_rhs)
    compatible_curl = discrete_curl_defects(3, 3, compatible_rhs)
    incompatible_curl = discrete_curl_defects(3, 3, incompatible_rhs)

    return {
        "description": (
            "Sparse scipy PDE probe for curvature-integrability: can source rows be integrated "
            "into local A_perp/R potentials on a grid?"
        ),
        "status": "sparse-pde-probe-only",
        "depends_on": "p0_bianchi_minimal_curvature_integrability_system",
        "tooling": ["numpy", "scipy.sparse", "scipy.sparse.linalg.lsqr"],
        "grid_shape": [3, 3],
        "compatible_probe": compatible,
        "incompatible_probe": incompatible,
        "compatible_curl_defect_norm": float(np.linalg.norm(compatible_curl)),
        "incompatible_curl_defect_norm": float(np.linalg.norm(incompatible_curl)),
        "compatible_curl_closed": bool(np.linalg.norm(compatible_curl) < 1e-12),
        "incompatible_curl_closed": bool(np.linalg.norm(incompatible_curl) < 1e-12),
        "compatible_case_closes": compatible["closed_at_tolerance"],
        "incompatible_case_closes": incompatible["closed_at_tolerance"],
        "gauge_fix_used": "anchor one potential value",
        "uses_observational_fit": False,
        "uses_posthoc_qcross": False,
        "source_rows_scope": "toy finite-difference curvature rows; not full Janus perturbations",
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The sparse path can test a real integrability obstruction: compatible curvature "
            "rows have zero discrete curl and integrate to a potential, while rows with a "
            "discrete curl defect do not. "
            "This is still a bounded probe until Janus perturbative F_relative rows are supplied."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Curvature Integrability Sparse PDE Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Tooling: {', '.join(payload['tooling'])}",
        f"Grid shape: {payload['grid_shape']}",
        f"Compatible case closes: {payload['compatible_case_closes']}",
        f"Incompatible case closes: {payload['incompatible_case_closes']}",
        f"Compatible curl closed: {payload['compatible_curl_closed']}",
        f"Incompatible curl closed: {payload['incompatible_curl_closed']}",
        f"Compatible curl defect norm: {payload['compatible_curl_defect_norm']:.12g}",
        f"Incompatible curl defect norm: {payload['incompatible_curl_defect_norm']:.12g}",
        f"Gauge fix used: {payload['gauge_fix_used']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses posthoc Q_cross: {payload['uses_posthoc_qcross']}",
        f"Source rows scope: {payload['source_rows_scope']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Probe Results",
        "",
        "| case | equations | unknowns | iterations | residual norm | closes |",
        "|---|---|---|---|---|---|",
    ]
    for name in ("compatible_probe", "incompatible_probe"):
        row = payload[name]
        lines.append(
            f"| {name} | {row['equation_count']} | {row['unknown_count']} | "
            f"{row['iterations']} | {row['residual_norm']:.12g} | {row['closed_at_tolerance']} |"
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
