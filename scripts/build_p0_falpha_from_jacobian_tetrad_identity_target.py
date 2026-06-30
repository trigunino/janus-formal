from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_falpha_from_jacobian_tetrad_identity_target.md")
JSON_PATH = Path("outputs/reports/p0_falpha_from_jacobian_tetrad_identity_target.json")
TOLERANCE = 1e-12


def build_smooth_matrices(
    n: int = 64,
    box_size: float = 2.0 * np.pi,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    x = np.arange(n) * box_size / n
    e_plus = np.zeros((n, 2, 2), dtype=float)
    e_minus = np.zeros((n, 2, 2), dtype=float)
    l_map = np.zeros((n, 2, 2), dtype=float)
    de_plus = np.zeros_like(e_plus)
    de_minus = np.zeros_like(e_minus)
    dl_map = np.zeros_like(l_map)
    e_plus[:, 0, 0] = 1.0 + 0.03 * np.sin(x)
    e_plus[:, 1, 1] = 1.0 + 0.02 * np.cos(x)
    e_minus[:, 0, 0] = 1.0 - 0.01 * np.cos(x)
    e_minus[:, 1, 1] = 1.0 + 0.015 * np.sin(x)
    l_map[:, 0, 0] = 1.0 + 0.02 * np.sin(x)
    l_map[:, 1, 1] = 1.0 - 0.025 * np.cos(x)
    l_map[:, 0, 1] = 0.01 * np.sin(2.0 * x)
    l_map[:, 1, 0] = 0.012 * np.cos(2.0 * x)
    de_plus[:, 0, 0] = 0.03 * np.cos(x)
    de_plus[:, 1, 1] = -0.02 * np.sin(x)
    de_minus[:, 0, 0] = 0.01 * np.sin(x)
    de_minus[:, 1, 1] = 0.015 * np.cos(x)
    dl_map[:, 0, 0] = 0.02 * np.cos(x)
    dl_map[:, 1, 1] = 0.025 * np.sin(x)
    dl_map[:, 0, 1] = 0.02 * np.cos(2.0 * x)
    dl_map[:, 1, 0] = -0.024 * np.sin(2.0 * x)
    jacobian = e_plus @ l_map @ e_minus
    return e_plus, e_minus, jacobian, de_plus, de_minus, dl_map


def reconstruct_l(e_plus: np.ndarray, e_minus: np.ndarray, jacobian: np.ndarray) -> np.ndarray:
    return np.linalg.inv(e_plus) @ jacobian @ np.linalg.inv(e_minus)


def dl_from_jacobian_identity(
    e_plus: np.ndarray,
    e_minus: np.ndarray,
    jacobian: np.ndarray,
    de_plus: np.ndarray,
    de_minus: np.ndarray,
    direct_dl: np.ndarray,
) -> dict:
    l_map = reconstruct_l(e_plus, e_minus, jacobian)
    d_j = de_plus @ l_map @ e_minus + e_plus @ direct_dl @ e_minus + e_plus @ l_map @ de_minus
    rhs = np.linalg.inv(e_plus) @ (
        d_j - de_plus @ l_map @ e_minus - e_plus @ l_map @ de_minus
    ) @ np.linalg.inv(e_minus)
    residual = direct_dl - rhs
    generator = direct_dl @ np.linalg.inv(l_map)
    return {
        "max_abs_dl_identity_residual": float(np.max(np.abs(residual))),
        "dl_identity_closes": bool(np.max(np.abs(residual)) < TOLERANCE),
        "max_abs_falpha_candidate": float(np.max(np.abs(generator))),
    }


def build_payload() -> dict:
    e_plus, e_minus, jacobian, de_plus, de_minus, dl_map = build_smooth_matrices()
    probe = dl_from_jacobian_identity(e_plus, e_minus, jacobian, de_plus, de_minus, dl_map)
    identity_rows = [
        {
            "id": "FJ-1",
            "identity": "J = e_plus L e_minus",
            "role": "turn a pointwise same-L map into a Jacobian-backed map candidate",
            "closed": probe["dl_identity_closes"],
        },
        {
            "id": "FJ-2",
            "identity": "D L = e_plus^-1 [D J - (D e_plus)L e_minus - e_plus L(D e_minus)] e_minus^-1",
            "role": "computes F_alpha=(D_alpha L)L^-1 from Jacobian and tetrad derivatives",
            "closed": probe["dl_identity_closes"],
        },
        {
            "id": "FJ-3",
            "identity": "D_[a J^mu_b]=0",
            "role": "needed before this F_alpha is source-derived rather than pointwise",
            "closed": False,
        },
    ]
    return {
        "description": "Jacobian/tetrad identity target for deriving F_alpha from a source-selected phi/L map.",
        "status": "falpha-from-jacobian-tetrad-identity-target-open",
        "depends_on": [
            "p0_cuu_jacobian_curl_numeric_probe",
            "p0_cuu_inverse_map_integrability_target",
        ],
        "identity_rows": identity_rows,
        "numeric_probe": probe,
        "dl_identity_written": True,
        "dl_identity_numeric_closes": probe["dl_identity_closes"],
        "jacobian_integrability_required": True,
        "source_selected_jacobian_found": False,
        "falpha_source_derived": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "D L can be computed from J and tetrad derivatives once a source-selected integrable "
            "J=dphi exists. The algebraic identity closes numerically, but F_alpha is still not "
            "source-derived because Janus has not selected that J/phi."
        ),
    }


def render_markdown(payload: dict) -> str:
    probe = payload["numeric_probe"]
    lines = [
        "# P0 Falpha From Jacobian/Tetrad Identity Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"DL identity written: {payload['dl_identity_written']}",
        f"DL identity numeric closes: {payload['dl_identity_numeric_closes']}",
        f"DL residual: {probe['max_abs_dl_identity_residual']:.12g}",
        f"Jacobian integrability required: {payload['jacobian_integrability_required']}",
        f"Source-selected Jacobian found: {payload['source_selected_jacobian_found']}",
        f"Falpha source-derived: {payload['falpha_source_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identity Rows",
        "",
        "| id | identity | role | closed |",
        "|---|---|---|---:|",
    ]
    for row in payload["identity_rows"]:
        lines.append(f"| {row['id']} | `{row['identity']}` | {row['role']} | {row['closed']} |")
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
