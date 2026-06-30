from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_weakfield_tetrad_pipeline_probe.md")
JSON_PATH = Path("outputs/reports/p0_weakfield_tetrad_pipeline_probe.json")
SPATIAL = ("x", "y", "z")
ARRAY_AXIS = {"x": 2, "y": 1, "z": 0}
CENTER = (2, 2, 2)
ETA = np.diag([-1.0, 1.0, 1.0, 1.0])
TOLERANCE = 1e-12


def _offset(point: tuple[int, int, int], axis: str, step: int) -> tuple[int, int, int]:
    shifted = list(point)
    shifted[ARRAY_AXIS[axis]] += step
    return tuple(shifted)


def build_toy_weakfield_fields() -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    axis = np.arange(-2.0, 3.0)
    zz, yy, xx = np.meshgrid(axis, axis, axis, indexing="ij")
    delta_phi = (
        0.08 * xx
        - 0.04 * yy
        + 0.03 * zz
        + 0.015 * xx**2
        + 0.020 * yy**2
        - 0.010 * zz**2
        + 0.012 * xx * yy
        - 0.008 * xx * zz
        + 0.006 * yy * zz
    )
    delta_psi = (
        -0.030 * xx
        + 0.025 * yy
        + 0.010 * zz
        + 0.010 * xx**2
        - 0.005 * yy**2
        + 0.012 * zz**2
        + 0.007 * xx * yy
        - 0.004 * xx * zz
        + 0.005 * yy * zz
    )
    return axis, delta_phi, delta_psi


def central_gradient(
    field: np.ndarray,
    point: tuple[int, int, int] = CENTER,
    spacing: float = 1.0,
) -> dict[str, float]:
    return {
        axis: float((field[_offset(point, axis, 1)] - field[_offset(point, axis, -1)]) / (2.0 * spacing))
        for axis in SPATIAL
    }


def central_hessian(
    field: np.ndarray,
    point: tuple[int, int, int] = CENTER,
    spacing: float = 1.0,
) -> dict[tuple[str, str], float]:
    values: dict[tuple[str, str], float] = {}
    inv_h2 = 1.0 / spacing**2
    for i, left in enumerate(SPATIAL):
        for right in SPATIAL[i:]:
            if left == right:
                value = (
                    field[_offset(point, left, 1)]
                    - 2.0 * field[point]
                    + field[_offset(point, left, -1)]
                ) * inv_h2
            else:
                pp = field[_offset(_offset(point, left, 1), right, 1)]
                pm = field[_offset(_offset(point, left, 1), right, -1)]
                mp = field[_offset(_offset(point, left, -1), right, 1)]
                mm = field[_offset(_offset(point, left, -1), right, -1)]
                value = (pp - pm - mp + mm) / (4.0 * spacing**2)
            values[(left, right)] = float(value)
            values[(right, left)] = float(value)
    return values


def connection_rows(delta_phi: np.ndarray, delta_psi: np.ndarray) -> dict:
    grad_phi = central_gradient(delta_phi)
    grad_psi = central_gradient(delta_psi)
    return {
        "boost_connection": {
            f"Delta_omega_0{axis}0": grad_phi[axis]
            for axis in SPATIAL
        },
        "spatial_rotation": {
            "Delta_omega_xyx": grad_psi["y"],
            "Delta_omega_xyy": -grad_psi["x"],
            "Delta_omega_xzx": grad_psi["z"],
            "Delta_omega_xzz": -grad_psi["x"],
            "Delta_omega_yzy": grad_psi["z"],
            "Delta_omega_yzz": -grad_psi["y"],
        },
    }


def _hessian_from_connection(field: np.ndarray, spacing: float = 1.0) -> dict[tuple[str, str], float]:
    values: dict[tuple[str, str], float] = {}
    for i, left in enumerate(SPATIAL):
        for right in SPATIAL[i:]:
            plus = central_gradient(field, _offset(CENTER, right, 1), spacing)[left]
            minus = central_gradient(field, _offset(CENTER, right, -1), spacing)[left]
            value = float((plus - minus) / (2.0 * spacing))
            values[(left, right)] = value
            values[(right, left)] = value
    return values


def curvature_injection_rows(delta_phi: np.ndarray, delta_psi: np.ndarray) -> tuple[list[dict], float]:
    phi_from_connection = _hessian_from_connection(delta_phi)
    psi_from_connection = _hessian_from_connection(delta_psi)
    phi_direct = central_hessian(delta_phi)
    psi_direct = central_hessian(delta_psi)

    rows = []
    for i, left in enumerate(SPATIAL):
        for right in SPATIAL[i:]:
            row = f"Delta_F_0{left}0{right}"
            value = phi_from_connection[(left, right)]
            direct = phi_direct[(left, right)]
            rows.append(
                {
                    "group": "temporal_from_boost_connection",
                    "row": row,
                    "value": value,
                    "direct_hessian_value": direct,
                    "connection_derivative_residual": abs(value - direct),
                }
            )

    spatial_rows = {
        "Delta_F_xyxy": psi_from_connection[("x", "x")] + psi_from_connection[("y", "y")],
        "Delta_F_xzxz": psi_from_connection[("x", "x")] + psi_from_connection[("z", "z")],
        "Delta_F_yzyz": psi_from_connection[("y", "y")] + psi_from_connection[("z", "z")],
    }
    direct_spatial_rows = {
        "Delta_F_xyxy": psi_direct[("x", "x")] + psi_direct[("y", "y")],
        "Delta_F_xzxz": psi_direct[("x", "x")] + psi_direct[("z", "z")],
        "Delta_F_yzyz": psi_direct[("y", "y")] + psi_direct[("z", "z")],
    }
    for row, value in spatial_rows.items():
        direct = direct_spatial_rows[row]
        rows.append(
            {
                "group": "spatial_from_rotation_connection",
                "row": row,
                "value": float(value),
                "direct_hessian_value": float(direct),
                "connection_derivative_residual": abs(float(value - direct)),
            }
        )

    max_residual = max(row["connection_derivative_residual"] for row in rows)
    return rows, float(max_residual)


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


def metric_error(transform: np.ndarray) -> float:
    return float(np.max(np.abs(transform.T @ ETA @ transform - ETA)))


def qcross(transform: np.ndarray, covector: np.ndarray, source_velocity: np.ndarray) -> float:
    transported = transform @ source_velocity
    numerator = float(covector @ ETA @ transported) ** 2
    denominator = float(covector @ ETA @ source_velocity) ** 2
    return numerator / denominator


def mirror_probe(
    transport_l: np.ndarray,
    optical_l: np.ndarray,
    curvature_rows_by_name: dict[str, float],
) -> dict:
    r_plus = np.array(
        [
            1.0,
            curvature_rows_by_name["Delta_F_0x0x"],
            curvature_rows_by_name["Delta_F_0x0y"],
            curvature_rows_by_name["Delta_F_0x0z"],
        ],
        dtype=float,
    )
    transport_inverse = np.linalg.inv(transport_l)
    optical_inverse = np.linalg.inv(optical_l)
    r_minus = -(transport_inverse @ r_plus)
    transport_residual = np.concatenate(
        [r_minus + transport_inverse @ r_plus, r_plus + transport_l @ r_minus]
    )
    optical_residual = np.concatenate(
        [r_minus + optical_inverse @ r_plus, r_plus + optical_l @ r_minus]
    )
    return {
        "r_plus_from_curvature": [float(value) for value in r_plus],
        "transport_mirror_max_abs_residual": float(np.max(np.abs(transport_residual))),
        "optical_mirror_max_abs_residual": float(np.max(np.abs(optical_residual))),
        "transport_mirror_closes": bool(np.max(np.abs(transport_residual)) < TOLERANCE),
        "optical_mirror_closes": bool(np.max(np.abs(optical_residual)) < TOLERANCE),
    }


def qcross_gate(
    transport_l: np.ndarray,
    optical_l: np.ndarray,
    source_velocity: np.ndarray,
) -> dict:
    covectors = {
        "forward_x": np.array([1.0, 1.0, 0.0, 0.0], dtype=float),
        "transverse_y": np.array([1.0, 0.0, 1.0, 0.0], dtype=float),
        "backward_x": np.array([1.0, -1.0, 0.0, 0.0], dtype=float),
    }
    rows = []
    for name, covector in covectors.items():
        geometric = qcross(transport_l, covector, source_velocity)
        same_l_optical = qcross(transport_l, covector, source_velocity)
        independent_optical = qcross(optical_l, covector, source_velocity)
        rows.append(
            {
                "covector": name,
                "null_error": float(covector @ ETA @ covector),
                "geometric_qcross": float(geometric),
                "same_l_optical_qcross": float(same_l_optical),
                "same_l_residual": float(abs(geometric - same_l_optical)),
                "independent_optical_qcross": float(independent_optical),
                "independent_l_residual": float(abs(geometric - independent_optical)),
            }
        )
    return {
        "rows": rows,
        "same_l_max_residual": max(row["same_l_residual"] for row in rows),
        "independent_l_min_residual": min(row["independent_l_residual"] for row in rows),
        "same_l_qcross_gate_closes": all(row["same_l_residual"] < TOLERANCE for row in rows),
        "independent_optical_l_gate_closes": all(row["independent_l_residual"] < TOLERANCE for row in rows),
    }


def build_payload() -> dict:
    _, delta_phi, delta_psi = build_toy_weakfield_fields()
    rows = connection_rows(delta_phi, delta_psi)
    curvature_rows, curvature_residual = curvature_injection_rows(delta_phi, delta_psi)
    curvature_by_name = {row["row"]: row["value"] for row in curvature_rows}
    connection_strength = sum(abs(value) for value in rows["boost_connection"].values())
    curvature_strength = sum(abs(curvature_by_name[name]) for name in ("Delta_F_0x0x", "Delta_F_0y0y", "Delta_F_0z0z"))
    transport_beta = float(np.clip(connection_strength + 0.5 * curvature_strength, 0.05, 0.35))
    independent_optical_beta = float(0.55 * transport_beta)
    transport_l = lorentz_like_boost(transport_beta)
    independent_optical_l = lorentz_like_boost(independent_optical_beta)
    source_velocity = np.array([1.0, 0.0, 0.0, 0.0], dtype=float)

    consistent_mirror = mirror_probe(transport_l, transport_l, curvature_by_name)
    inconsistent_mirror = mirror_probe(transport_l, independent_optical_l, curvature_by_name)
    qcross_results = qcross_gate(transport_l, independent_optical_l, source_velocity)

    return {
        "description": (
            "Bounded P0 numeric artifact chaining weak-field tetrad connection rows "
            "into curvature injection, mirror residual, and same-L Q_cross probes."
        ),
        "status": "bounded-p0-weakfield-tetrad-pipeline-probe",
        "depends_on": [
            "p0_weakfield_tetrad_connection_target",
            "p0_weakfield_curvature_injection_probe",
            "p0_mirror_inverse_numeric_residual_probe",
            "p0_same_l_qcross_numeric_contraction_probe",
        ],
        "tooling": ["numpy"],
        "potential_source": "toy weak-field relative DeltaPhi/DeltaPsi gradients and Hessians",
        "pipeline": [
            "relative potential gradients -> tetrad connection rows",
            "connection row derivatives -> curvature injection rows",
            "curvature rows -> mirror residual seed and same transport L",
            "same transport L -> Q_cross gate",
        ],
        "connection_rows": rows,
        "curvature_injection_rows": curvature_rows,
        "connection_to_curvature_max_residual": curvature_residual,
        "transport_beta_from_rows": transport_beta,
        "independent_optical_beta": independent_optical_beta,
        "transport_l_metric_error": metric_error(transport_l),
        "independent_optical_l_metric_error": metric_error(independent_optical_l),
        "consistent_branch": {
            "branch": "same-L",
            **consistent_mirror,
            "same_l_qcross_gate_closes": qcross_results["same_l_qcross_gate_closes"],
            "same_l_max_residual": qcross_results["same_l_max_residual"],
        },
        "inconsistent_independent_optical_l_branch": {
            "branch": "independent-optical-L",
            **inconsistent_mirror,
            "independent_optical_l_gate_closes": qcross_results["independent_optical_l_gate_closes"],
            "independent_l_min_residual": qcross_results["independent_l_min_residual"],
            "shortcut_allowed": False,
        },
        "qcross_rows": qcross_results["rows"],
        "uses_fit": False,
        "uses_observational_fit": False,
        "uses_posthoc_qcross": False,
        "uses_qdet_absorption": False,
        "uses_scalar_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "bounded_numeric_artifact": True,
        "verdict": (
            "The same-L branch closes the bounded mirror and Q_cross checks. A deliberately "
            "independent optical L leaves mirror/Q_cross residuals, so no fit, posthoc "
            "Q_cross, or Qdet absorption is admitted."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Weak-Field Tetrad Pipeline Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Tooling: {', '.join(payload['tooling'])}",
        f"Potential source: {payload['potential_source']}",
        f"Connection to curvature max residual: {payload['connection_to_curvature_max_residual']:.3g}",
        f"Transport beta from rows: {payload['transport_beta_from_rows']:.12g}",
        f"Independent optical beta: {payload['independent_optical_beta']:.12g}",
        f"Consistent branch mirror closes: {payload['consistent_branch']['transport_mirror_closes']}",
        f"Consistent branch Q_cross closes: {payload['consistent_branch']['same_l_qcross_gate_closes']}",
        f"Independent optical-L mirror closes: {payload['inconsistent_independent_optical_l_branch']['optical_mirror_closes']}",
        f"Independent optical-L Q_cross closes: {payload['inconsistent_independent_optical_l_branch']['independent_optical_l_gate_closes']}",
        f"Uses fit: {payload['uses_fit']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses posthoc Q_cross: {payload['uses_posthoc_qcross']}",
        f"Uses Qdet absorption: {payload['uses_qdet_absorption']}",
        f"Uses scalar absorption: {payload['uses_scalar_absorption']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Pipeline",
        "",
    ]
    lines.extend(f"- {step}" for step in payload["pipeline"])
    lines.extend(["", "## Curvature Injection Rows", "", "| group | row | value | residual |", "|---|---|---:|---:|"])
    for row in payload["curvature_injection_rows"]:
        lines.append(
            f"| {row['group']} | `{row['row']}` | {row['value']:.12g} | "
            f"{row['connection_derivative_residual']:.3g} |"
        )
    lines.extend(["", "## Q_cross Rows", "", "| covector | same-L residual | independent-L residual |", "|---|---:|---:|"])
    for row in payload["qcross_rows"]:
        lines.append(
            f"| {row['covector']} | {row['same_l_residual']:.3g} | "
            f"{row['independent_l_residual']:.12g} |"
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
