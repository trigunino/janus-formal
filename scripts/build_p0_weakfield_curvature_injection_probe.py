from __future__ import annotations

from pathlib import Path
import json
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_bianchi_minimal_curvature_numeric_probe import solve_linear_probe
from scripts.build_p0_janus_weakfield_delta_phi_psi_source_chain_gate import (
    build_payload as build_delta_phi_psi_source_chain,
)


REPORT_PATH = Path("outputs/reports/p0_weakfield_curvature_injection_probe.md")
JSON_PATH = Path("outputs/reports/p0_weakfield_curvature_injection_probe.json")


def build_reference_potentials() -> tuple[np.ndarray, np.ndarray]:
    axis = np.arange(5, dtype=float)
    yy, xx = np.meshgrid(axis, axis, indexing="ij")
    phi_plus = 0.02 * xx + 0.01 * yy
    relative = (
        0.08 * xx**2
        + 0.03 * yy**2
        + 0.04 * xx * yy
        + 0.01 * xx**3
        - 0.015 * yy**3
        + 0.02 * xx * yy**2
    )
    return phi_plus, phi_plus + relative


def build_reference_metric_potentials() -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    phi_plus, phi_minus = build_reference_potentials()
    axis = np.arange(5, dtype=float)
    yy, xx = np.meshgrid(axis, axis, indexing="ij")
    psi_plus = -0.01 * xx + 0.015 * yy
    relative_psi = 0.04 * xx**2 - 0.02 * yy**2 + 0.03 * xx * yy + 0.005 * xx**3
    return phi_plus, phi_minus, psi_plus, psi_plus + relative_psi


def build_curvature_injection_system(
    potential_minus: np.ndarray,
    potential_plus: np.ndarray,
    spacing: float = 1.0,
) -> tuple[np.ndarray, np.ndarray, list[dict]]:
    if potential_minus.shape != potential_plus.shape or potential_minus.ndim != 2:
        raise ValueError("potential grids must be matching 2D arrays")
    if min(potential_minus.shape) < 3:
        raise ValueError("potential grids need at least one interior point")
    if spacing <= 0.0:
        raise ValueError("spacing must be positive")

    ny, nx = potential_minus.shape
    delta = np.asarray(potential_minus - potential_plus, dtype=float)
    rows: list[np.ndarray] = []
    rhs: list[float] = []
    metadata: list[dict] = []
    inv_h2 = 1.0 / spacing**2

    def idx(y: int, x: int) -> int:
        return y * nx + x

    def add_row(point: tuple[int, int], component: str, coeffs: list[tuple[int, int, float]]) -> None:
        row = np.zeros(nx * ny, dtype=float)
        value = 0.0
        for y, x, weight in coeffs:
            scaled = weight * inv_h2
            row[idx(y, x)] += scaled
            value += scaled * float(delta[y, x])
        rows.append(row)
        rhs.append(value)
        metadata.append({"point": [point[0], point[1]], "component": component, "value": value})

    for y in range(1, ny - 1):
        for x in range(1, nx - 1):
            dxx = [(y, x + 1, 1.0), (y, x, -2.0), (y, x - 1, 1.0)]
            dyy = [(y + 1, x, 1.0), (y, x, -2.0), (y - 1, x, 1.0)]
            dxy = [
                (y + 1, x + 1, 0.25),
                (y + 1, x - 1, -0.25),
                (y - 1, x + 1, -0.25),
                (y - 1, x - 1, 0.25),
            ]
            add_row((y, x), "dxx", dxx)
            add_row((y, x), "dxy", dxy)
            add_row((y, x), "dyy", dyy)
            add_row((y, x), "laplacian", dxx + dyy)

    return np.vstack(rows), np.array(rhs, dtype=float), metadata


def build_two_potential_curvature_injection_system(
    phi_minus: np.ndarray,
    phi_plus: np.ndarray,
    psi_minus: np.ndarray,
    psi_plus: np.ndarray,
    spacing: float = 1.0,
) -> tuple[np.ndarray, np.ndarray, list[dict]]:
    phi_matrix, phi_rhs, phi_rows = build_curvature_injection_system(phi_minus, phi_plus, spacing)
    psi_matrix, psi_rhs, psi_rows = build_curvature_injection_system(psi_minus, psi_plus, spacing)
    if phi_matrix.shape[1] != psi_matrix.shape[1]:
        raise ValueError("Phi/Psi grids must produce matching unknown counts")

    zero_phi = np.zeros_like(phi_matrix)
    zero_psi = np.zeros_like(psi_matrix)
    matrix = np.vstack(
        [
            np.hstack([phi_matrix, zero_phi]),
            np.hstack([zero_psi, psi_matrix]),
        ]
    )
    rhs = np.concatenate([phi_rhs, psi_rhs])
    metadata = [
        {**row, "source": "Delta_Phi", "weakfield_role": "temporal_tidal"}
        for row in phi_rows
    ] + [
        {**row, "source": "Delta_Psi", "weakfield_role": "spatial_tidal"}
        for row in psi_rows
    ]
    return matrix, rhs, metadata


def inject_curl_defect(rhs: np.ndarray, metadata: list[dict], amount: float = 0.25) -> tuple[np.ndarray, dict]:
    defected = np.array(rhs, dtype=float, copy=True)
    center = np.median([row["point"] for row in metadata], axis=0).astype(int).tolist()
    for index, row in enumerate(metadata):
        if row["component"] == "dxy" and row["point"] == center:
            defected[index] += amount
            return defected, {
                "row_index": index,
                "point": row["point"],
                "component": row["component"],
                "amount": float(amount),
                "defect_type": "discrete-curl-mixed-derivative-row",
            }
    raise ValueError("no central dxy row found")


def build_payload() -> dict:
    source_chain = build_delta_phi_psi_source_chain()
    phi_plus, phi_minus = build_reference_potentials()
    matrix, rhs, rows = build_curvature_injection_system(phi_minus, phi_plus)
    defected_rhs, defect = inject_curl_defect(rhs, rows)
    metric_phi_plus, metric_phi_minus, psi_plus, psi_minus = build_reference_metric_potentials()
    two_potential_matrix, two_potential_rhs, two_potential_rows = build_two_potential_curvature_injection_system(
        metric_phi_minus,
        metric_phi_plus,
        psi_minus,
        psi_plus,
    )

    integrable = solve_linear_probe(matrix, rhs)
    curl_defected = solve_linear_probe(matrix, defected_rhs)
    two_potential = solve_linear_probe(two_potential_matrix, two_potential_rhs)

    return {
        "description": (
            "Bounded numeric weak-field curvature injection probe: finite-difference "
            "Hessian/Laplacian rows are computed from Delta_Phi and Delta_Psi and "
            "injected through the existing dense scipy linear probe."
        ),
        "status": "bounded-numeric-curvature-injection-probe",
        "depends_on": [
            "p0_janus_weakfield_delta_phi_psi_source_chain_gate",
            "p0_weakfield_relative_curvature_rows_target",
            "p0_bianchi_minimal_curvature_numeric_probe",
            "p0_curvature_integrability_sparse_pde_probe",
        ],
        "source_chain_artifact": "p0_janus_weakfield_delta_phi_psi_source_chain_gate",
        "source_chain_delta_psi_row_derived": bool(source_chain["delta_psi_poisson_row_derived"]),
        "source_chain_general_slip_closed": bool(source_chain["general_slip_source_closed"]),
        "tooling": ["numpy", "scipy.linalg.lstsq via solve_linear_probe"],
        "potential_source": "Phi_minus-Phi_plus",
        "metric_potential_sources": ["Delta_Phi", "Delta_Psi"],
        "grid_shape": list(phi_plus.shape),
        "row_components": ["dxx", "dxy", "dyy", "laplacian"],
        "row_count": len(rows),
        "two_potential_row_count": len(two_potential_rows),
        "unknown_vector": "relative_potential_grid_nodes",
        "two_potential_unknown_vector": "Delta_Phi_grid_nodes + Delta_Psi_grid_nodes",
        "probe_matrix_shape": list(matrix.shape),
        "two_potential_probe_matrix_shape": list(two_potential_matrix.shape),
        "integrable_probe": integrable,
        "curl_defected_probe": curl_defected,
        "two_potential_probe": two_potential,
        "integrable_case_closes": integrable["closed_at_tolerance"],
        "curl_defected_case_closes": curl_defected["closed_at_tolerance"],
        "two_potential_case_closes": two_potential["closed_at_tolerance"],
        "curl_defect": defect,
        "row_sample": rows[:4],
        "two_potential_row_sample": two_potential_rows[:8],
        "uses_observational_fit": False,
        "uses_posthoc_qcross": False,
        "uses_scalar_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Finite-difference rows sourced by weak-field Delta_Phi/Delta_Psi integrate, "
            "while a deliberately curl-defected mixed row leaves a residual. This is a "
            "pipeline probe only, not an observational fit or scalar absorption route."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Weak-Field Curvature Injection Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Source chain artifact: `{payload['source_chain_artifact']}`",
        f"Source chain Delta Psi row derived: {payload['source_chain_delta_psi_row_derived']}",
        f"Source chain general slip closed: {payload['source_chain_general_slip_closed']}",
        f"Tooling: {', '.join(payload['tooling'])}",
        f"Potential source: {payload['potential_source']}",
        f"Metric potential sources: {payload['metric_potential_sources']}",
        f"Grid shape: {payload['grid_shape']}",
        f"Row components: {payload['row_components']}",
        f"Row count: {payload['row_count']}",
        f"Two-potential row count: {payload['two_potential_row_count']}",
        f"Probe matrix shape: {payload['probe_matrix_shape']}",
        f"Two-potential probe matrix shape: {payload['two_potential_probe_matrix_shape']}",
        f"Integrable case closes: {payload['integrable_case_closes']}",
        f"Curl-defected case closes: {payload['curl_defected_case_closes']}",
        f"Two-potential case closes: {payload['two_potential_case_closes']}",
        f"Curl defect: {payload['curl_defect']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses posthoc Q_cross: {payload['uses_posthoc_qcross']}",
        f"Uses scalar absorption: {payload['uses_scalar_absorption']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Probe Results",
        "",
        "| case | equations | unknowns | rank | residual norm | closes |",
        "|---|---|---|---|---|---|",
    ]
    for name in ("integrable_probe", "curl_defected_probe", "two_potential_probe"):
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
