from __future__ import annotations

from pathlib import Path
import json

import numpy as np
from scipy import linalg


REPORT_PATH = Path("outputs/reports/p0_mirror_inverse_numeric_residual_probe.md")
JSON_PATH = Path("outputs/reports/p0_mirror_inverse_numeric_residual_probe.json")
TOLERANCE = 1e-10


def reference_l_pm() -> np.ndarray:
    return np.array([[2.0, 0.5], [0.0, 1.5]], dtype=float)


def pack_state(
    r_pm: np.ndarray,
    r_mp: np.ndarray,
    l_mp: np.ndarray,
    log_b_pm: float,
    log_b_mp: float,
) -> np.ndarray:
    return np.concatenate(
        [
            np.asarray(r_pm, dtype=float),
            np.asarray(r_mp, dtype=float),
            np.asarray(l_mp, dtype=float).reshape(-1),
            np.array([log_b_pm, log_b_mp], dtype=float),
        ]
    )


def consistency_blocks(l_pm: np.ndarray) -> list[dict]:
    l_mp = linalg.inv(l_pm)
    block_count = 10

    r_mp_from_pm = np.zeros((2, block_count), dtype=float)
    r_mp_from_pm[:, 0:2] = l_mp
    r_mp_from_pm[:, 2:4] = np.eye(2)

    r_pm_from_mp = np.zeros((2, block_count), dtype=float)
    r_pm_from_mp[:, 0:2] = np.eye(2)
    r_pm_from_mp[:, 2:4] = l_pm

    inverse_l = np.zeros((4, block_count), dtype=float)
    inverse_l[:, 4:8] = np.eye(4)

    reciprocal_b = np.zeros((1, block_count), dtype=float)
    reciprocal_b[0, 8:10] = 1.0

    return [
        {
            "name": "R_mp_plus_L_mp_R_pm",
            "equation": "R_mp + L_mp R_pm = 0",
            "matrix": r_mp_from_pm,
            "rhs": np.zeros(2, dtype=float),
        },
        {
            "name": "R_pm_plus_L_pm_R_mp",
            "equation": "R_pm + L_pm R_mp = 0",
            "matrix": r_pm_from_mp,
            "rhs": np.zeros(2, dtype=float),
        },
        {
            "name": "inverse_L_mp",
            "equation": "L_mp = inverse(L_pm)",
            "matrix": inverse_l,
            "rhs": l_mp.reshape(-1),
        },
        {
            "name": "reciprocal_B_4vol",
            "equation": "log B_4vol_pm + log B_4vol_mp = 0",
            "matrix": reciprocal_b,
            "rhs": np.zeros(1, dtype=float),
        },
    ]


def _to_float_list(values: np.ndarray) -> list[float]:
    return [float(value) for value in np.asarray(values, dtype=float).reshape(-1)]


def summarize_block(block: dict, state: np.ndarray) -> dict:
    matrix = block["matrix"]
    rhs = block["rhs"]
    residual = matrix @ state - rhs
    return {
        "name": block["name"],
        "equation": block["equation"],
        "matrix": [[float(value) for value in row] for row in matrix],
        "rhs": _to_float_list(rhs),
        "matrix_shape": list(matrix.shape),
        "rank": int(np.linalg.matrix_rank(matrix)),
        "residual_vector": _to_float_list(residual),
        "residual_norm": float(linalg.norm(residual)),
        "max_abs_residual": float(np.max(np.abs(residual))),
        "closed_at_tolerance": bool(linalg.norm(residual) < TOLERANCE),
    }


def evaluate_probe(blocks: list[dict], state: np.ndarray) -> dict:
    block_results = [summarize_block(block, state) for block in blocks]
    residual = np.concatenate([np.array(row["residual_vector"], dtype=float) for row in block_results])
    row_blocks = [row for row in block_results if row["name"].startswith("R_")]
    return {
        "block_results": block_results,
        "residual_norm": float(linalg.norm(residual)),
        "max_abs_residual": float(np.max(np.abs(residual))),
        "closed_at_tolerance": bool(linalg.norm(residual) < TOLERANCE),
        "mirrored_rows_close": all(row["closed_at_tolerance"] for row in row_blocks),
        "inverse_l_closes": block_results[2]["closed_at_tolerance"],
        "reciprocal_b4vol_closes": block_results[3]["closed_at_tolerance"],
    }


def build_payload() -> dict:
    l_pm = reference_l_pm()
    l_mp = linalg.inv(l_pm)
    r_pm = np.array([0.3, -0.6], dtype=float)
    r_mp_compatible = -(l_mp @ r_pm)
    r_mp_inconsistent = r_mp_compatible + np.array([0.1, 0.0], dtype=float)
    log_b_pm = float(np.log(1.2))
    log_b_mp = -log_b_pm
    blocks = consistency_blocks(l_pm)

    compatible_state = pack_state(r_pm, r_mp_compatible, l_mp, log_b_pm, log_b_mp)
    inconsistent_state = pack_state(r_pm, r_mp_inconsistent, l_mp, log_b_pm, log_b_mp)
    compatible = evaluate_probe(blocks, compatible_state)
    inconsistent = evaluate_probe(blocks, inconsistent_state)

    return {
        "description": (
            "Bounded P0 numeric residual probe for mirror-inverse consistency after "
            "curvature integrability. It evaluates fixed consistency matrices for "
            "R_pm/R_mp, inverse L, and reciprocal B_4vol without fitting."
        ),
        "status": "numeric-residual-probe-only",
        "depends_on": [
            "p0_bianchi_minimal_curvature_integrability_system",
            "p0_bianchi_minimal_mirror_inverse_attempt",
        ],
        "tooling": ["numpy", "scipy.linalg"],
        "unknown_vector": [
            "R_pm_0",
            "R_pm_1",
            "R_mp_0",
            "R_mp_1",
            "L_mp_00",
            "L_mp_01",
            "L_mp_10",
            "L_mp_11",
            "log_B_4vol_pm",
            "log_B_4vol_mp",
        ],
        "l_pm": [[float(value) for value in row] for row in l_pm],
        "expected_l_mp": [[float(value) for value in row] for row in l_mp],
        "reciprocal_b4vol": {
            "B_4vol_pm": 1.2,
            "B_4vol_mp": float(1.0 / 1.2),
            "log_B_4vol_pm": log_b_pm,
            "log_B_4vol_mp": log_b_mp,
        },
        "compatible_probe": compatible,
        "inconsistent_rows_probe": inconsistent,
        "compatible_mirrored_rows_close": compatible["mirrored_rows_close"],
        "inconsistent_mirrored_rows_close": inconsistent["mirrored_rows_close"],
        "inverse_l_relation_matrix_encoded": True,
        "reciprocal_b4vol_matrix_encoded": True,
        "uses_fit": False,
        "scalar_absorption_allowed": False,
        "bounded_numeric_artifact": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The fixed matrices distinguish compatible mirrored residual rows from an "
            "inconsistent R_mp row while reciprocal B_4vol and inverse L remain satisfied. "
            "No fit, scalar absorption, or physics closure is claimed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Mirror-Inverse Numeric Residual Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {', '.join(payload['depends_on'])}",
        f"Tooling: {', '.join(payload['tooling'])}",
        f"Unknown vector: {payload['unknown_vector']}",
        f"Compatible mirrored rows close: {payload['compatible_mirrored_rows_close']}",
        f"Inconsistent mirrored rows close: {payload['inconsistent_mirrored_rows_close']}",
        f"Inverse L relation matrix encoded: {payload['inverse_l_relation_matrix_encoded']}",
        f"Reciprocal B_4vol matrix encoded: {payload['reciprocal_b4vol_matrix_encoded']}",
        f"Uses fit: {payload['uses_fit']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Probe Results",
        "",
        "| case | residual norm | max abs residual | mirrored rows close | inverse L closes | B_4vol closes |",
        "|---|---|---|---|---|---|",
    ]
    for name in ("compatible_probe", "inconsistent_rows_probe"):
        row = payload[name]
        lines.append(
            f"| {name} | {row['residual_norm']:.12g} | {row['max_abs_residual']:.12g} | "
            f"{row['mirrored_rows_close']} | {row['inverse_l_closes']} | "
            f"{row['reciprocal_b4vol_closes']} |"
        )
    lines.extend(["", "## Consistency Blocks", "", "| name | equation | shape |", "|---|---|---|"])
    for row in payload["compatible_probe"]["block_results"]:
        lines.append(f"| {row['name']} | `{row['equation']}` | {row['matrix_shape']} |")
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
