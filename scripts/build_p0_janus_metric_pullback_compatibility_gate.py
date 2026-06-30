from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_janus_metric_pullback_compatibility_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_metric_pullback_compatibility_gate.json")
ETA2 = np.diag([-1.0, 1.0])
TOLERANCE = 1e-12


def coframe_from_metric_scales(a_time: float, a_space: float) -> np.ndarray:
    return np.diag([np.sqrt(a_time), np.sqrt(a_space)])


def frame_from_metric_scales(a_time: float, a_space: float) -> np.ndarray:
    return np.linalg.inv(coframe_from_metric_scales(a_time, a_space))


def metric_from_scales(a_time: float, a_space: float) -> np.ndarray:
    return np.diag([-a_time, a_space])


def solder_l(jac_self_to_other: np.ndarray, coframe_self: np.ndarray, frame_other: np.ndarray) -> np.ndarray:
    return coframe_self @ np.linalg.inv(jac_self_to_other) @ frame_other


def metric_pullback_residual(
    jac_self_to_other: np.ndarray,
    metric_self: np.ndarray,
    metric_other: np.ndarray,
) -> np.ndarray:
    return metric_self - jac_self_to_other.T @ metric_other @ jac_self_to_other


def lorentz_residual_from_l(transform: np.ndarray) -> np.ndarray:
    return transform.T @ ETA2 @ transform - ETA2


def lorentz_residual_from_metric_residual(
    jac_self_to_other: np.ndarray,
    frame_other: np.ndarray,
    metric_residual: np.ndarray,
) -> np.ndarray:
    inv_jac = np.linalg.inv(jac_self_to_other)
    return frame_other.T @ inv_jac.T @ metric_residual @ inv_jac @ frame_other


def max_abs(matrix: np.ndarray) -> float:
    return float(np.max(np.abs(matrix)))


def summarize_case(
    name: str,
    jac: np.ndarray,
    metric_self: np.ndarray,
    metric_other: np.ndarray,
    coframe_self: np.ndarray,
    frame_other: np.ndarray,
) -> dict:
    l_solder = solder_l(jac, coframe_self, frame_other)
    metric_residual = metric_pullback_residual(jac, metric_self, metric_other)
    direct_lorentz = lorentz_residual_from_l(l_solder)
    identity_lorentz = lorentz_residual_from_metric_residual(jac, frame_other, metric_residual)
    return {
        "case": name,
        "metric_pullback_residual_max": max_abs(metric_residual),
        "direct_lorentz_residual_max": max_abs(direct_lorentz),
        "identity_lorentz_residual_max": max_abs(identity_lorentz),
        "identity_error_max": max_abs(direct_lorentz - identity_lorentz),
        "metric_compatible": max_abs(metric_residual) < TOLERANCE,
        "lorentz_compatible": max_abs(direct_lorentz) < TOLERANCE,
    }


def build_payload() -> dict:
    jac = np.diag([1.2, 0.8])
    metric_other = ETA2.copy()
    metric_self_compatible = jac.T @ metric_other @ jac
    compatible = summarize_case(
        "compatible_pullback",
        jac,
        metric_self_compatible,
        metric_other,
        coframe_from_metric_scales(1.44, 0.64),
        frame_from_metric_scales(1.0, 1.0),
    )

    identity = np.eye(2)
    mismatch = summarize_case(
        "mismatched_metrics",
        identity,
        metric_from_scales(1.0, 1.0),
        metric_from_scales(1.002, 0.998),
        coframe_from_metric_scales(1.0, 1.0),
        frame_from_metric_scales(1.002, 0.998),
    )
    theorem_rows = [
        {
            "name": "metric_definitions",
            "formula": "g_s=theta_s^T eta theta_s and g_o=theta_o^T eta theta_o",
            "closed": True,
        },
        {
            "name": "soldered_l",
            "formula": "L_{o->s}=theta_s J_{s->o}^{-1} e_o",
            "closed": True,
        },
        {
            "name": "residual_identity",
            "formula": "L^T eta L-eta=e_o^T J^{-T}(g_s-J^T g_o J)J^{-1}e_o",
            "closed": True,
        },
        {
            "name": "iff_condition",
            "formula": "for invertible J and e_o, L is Lorentz iff g_s=J^T g_o J",
            "closed": True,
        },
        {
            "name": "janus_selection_gate",
            "formula": "Janus must source-select phi so g_self=phi^*g_other, or pure soldered-L is rejected",
            "closed": False,
        },
    ]
    return {
        "description": "Metric pullback compatibility theorem for the soldered Janus same-L route.",
        "status": "metric-pullback-compatibility-derived-source-selection-open",
        "depends_on": [
            "p0_janus_soldered_l_substitution_residual_gate",
            "p0_janus_metric_tetrad_source_branch_gate",
            "p0_shared_phi_j_source_selection_gate",
            "p0_janus_metric_pullback_phi_selector_gate",
        ],
        "theorem_rows": theorem_rows,
        "compatible_case": compatible,
        "mismatch_case": mismatch,
        "residual_identity_proved_numeric": (
            compatible["identity_error_max"] < TOLERANCE
            and mismatch["identity_error_max"] < TOLERANCE
        ),
        "metric_pullback_iff_lorentz": True,
        "compatible_case_closes": bool(
            compatible["metric_compatible"] and compatible["lorentz_compatible"]
        ),
        "mismatch_case_rejected": bool(
            not mismatch["metric_compatible"] and not mismatch["lorentz_compatible"]
        ),
        "janus_source_selects_metric_pullback": False,
        "phi_selector_artifact": "p0_janus_metric_pullback_phi_selector_gate",
        "phi_selector_equation_derived": True,
        "pure_soldered_l_conditionally_admissible": True,
        "pure_soldered_l_generally_closed": False,
        "requires_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The compatibility condition is now derived: for the soldered map, Lorentz "
            "admissibility is equivalent to g_self=phi^*g_other. This is a theorem, not a "
            "fit. The remaining Janus task is to source-select such a phi or reject the "
            "pure soldered-L route outside metric-compatible branches."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Metric Pullback Compatibility Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Residual identity proved numeric: {payload['residual_identity_proved_numeric']}",
        f"Metric pullback iff Lorentz: {payload['metric_pullback_iff_lorentz']}",
        f"Compatible case closes: {payload['compatible_case_closes']}",
        f"Mismatch case rejected: {payload['mismatch_case_rejected']}",
        f"Janus source selects metric pullback: {payload['janus_source_selects_metric_pullback']}",
        f"Phi selector artifact: `{payload['phi_selector_artifact']}`",
        f"Phi selector equation derived: {payload['phi_selector_equation_derived']}",
        f"Pure soldered-L conditionally admissible: {payload['pure_soldered_l_conditionally_admissible']}",
        f"Pure soldered-L generally closed: {payload['pure_soldered_l_generally_closed']}",
        f"Requires observational fit: {payload['requires_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Theorem Rows",
        "",
        "| name | formula | closed |",
        "|---|---|---:|",
    ]
    for row in payload["theorem_rows"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['closed']} |")
    lines.extend(
        [
            "",
            "## Numeric Cases",
            "",
            "| case | metric residual | direct Lorentz residual | identity error | metric compatible | Lorentz compatible |",
            "|---|---:|---:|---:|---:|---:|",
        ]
    )
    for key in ("compatible_case", "mismatch_case"):
        row = payload[key]
        lines.append(
            f"| {row['case']} | {row['metric_pullback_residual_max']:.12g} | "
            f"{row['direct_lorentz_residual_max']:.12g} | {row['identity_error_max']:.12g} | "
            f"{row['metric_compatible']} | {row['lorentz_compatible']} |"
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
