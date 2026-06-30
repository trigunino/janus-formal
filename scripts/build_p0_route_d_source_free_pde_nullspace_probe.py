from __future__ import annotations

from pathlib import Path
import json

import numpy as np
from scipy import linalg


REPORT_PATH = Path("outputs/reports/p0_route_d_source_free_pde_nullspace_probe.md")
JSON_PATH = Path("outputs/reports/p0_route_d_source_free_pde_nullspace_probe.json")
TOLERANCE = 1e-10


def periodic_laplacian(size: int) -> np.ndarray:
    matrix = np.zeros((size, size), dtype=float)
    for row in range(size):
        matrix[row, row] = -2.0
        matrix[row, (row - 1) % size] = 1.0
        matrix[row, (row + 1) % size] = 1.0
    return matrix


def dirichlet_laplacian(size: int) -> np.ndarray:
    matrix = np.zeros((size, size), dtype=float)
    for row in range(size):
        matrix[row, row] = -2.0
        if row > 0:
            matrix[row, row - 1] = 1.0
        if row < size - 1:
            matrix[row, row + 1] = 1.0
    return matrix


def summarize_matrix(name: str, matrix: np.ndarray, source_supplied: bool) -> dict:
    singular_values = linalg.svdvals(matrix)
    rank = int(np.sum(singular_values > TOLERANCE))
    nullity = int(matrix.shape[1] - rank)
    return {
        "name": name,
        "shape": list(matrix.shape),
        "rank": rank,
        "nullity": nullity,
        "min_singular_value": float(np.min(singular_values)),
        "source_or_boundary_supplied": source_supplied,
        "selector_defect": bool(nullity > 0 or not source_supplied),
    }


def build_payload() -> dict:
    size = 6
    periodic = periodic_laplacian(size)
    dirichlet = dirichlet_laplacian(size)
    massive_periodic = periodic - 0.25 * np.eye(size)
    biharmonic_periodic = periodic @ periodic
    matrix_rows = [
        summarize_matrix("periodic_laplacian_source_free", periodic, False),
        summarize_matrix("dirichlet_laplacian_boundary_free", dirichlet, False),
        summarize_matrix("massive_periodic_free_mass", massive_periodic, False),
        summarize_matrix("periodic_biharmonic_source_free", biharmonic_periodic, False),
        summarize_matrix("source_fixed_operator_placeholder", dirichlet, True),
    ]
    return {
        "description": (
            "Route D numeric nullspace probe for source-free derivative PDE selectors. "
            "It distinguishes actual operator invertibility from Janus provenance: "
            "invertible matrices still fail zero-axiom selection when boundary data "
            "or coefficients are not source supplied."
        ),
        "status": "source-free-pde-nullspace-probe-open",
        "tooling": ["numpy", "scipy.linalg.svdvals"],
        "matrix_rows": matrix_rows,
        "periodic_kernel_detected": matrix_rows[0]["nullity"] > 0,
        "dirichlet_invertible_but_boundary_unsourced": (
            matrix_rows[1]["nullity"] == 0 and not matrix_rows[1]["source_or_boundary_supplied"]
        ),
        "mass_term_invertible_but_coefficient_unsourced": (
            matrix_rows[2]["nullity"] == 0 and not matrix_rows[2]["source_or_boundary_supplied"]
        ),
        "source_fixed_placeholder_passes_nullspace_only": not matrix_rows[4]["selector_defect"],
        "source_fixed_placeholder_is_janus_proof": False,
        "source_free_pde_excluded_as_no_axiom_selector": True,
        "full_no_go_proved": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Source-free derivative PDEs fail as zero-axiom selectors either because "
            "a nullspace survives or because invertibility was obtained by unsourced "
            "boundary/coefficient choices. A source-fixed operator still needs Janus "
            "provenance; this is a filter, not a full no-go theorem."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route D Source-Free PDE Nullspace Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Periodic kernel detected: {payload['periodic_kernel_detected']}",
        f"Dirichlet invertible but boundary unsourced: {payload['dirichlet_invertible_but_boundary_unsourced']}",
        f"Mass term invertible but coefficient unsourced: {payload['mass_term_invertible_but_coefficient_unsourced']}",
        f"Source-free PDE excluded as no-axiom selector: {payload['source_free_pde_excluded_as_no_axiom_selector']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| name | shape | rank | nullity | min singular | source/boundary supplied | selector defect |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for row in payload["matrix_rows"]:
        lines.append(
            f"| {row['name']} | {row['shape']} | {row['rank']} | {row['nullity']} | "
            f"{row['min_singular_value']:.3g} | {row['source_or_boundary_supplied']} | "
            f"{row['selector_defect']} |"
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
