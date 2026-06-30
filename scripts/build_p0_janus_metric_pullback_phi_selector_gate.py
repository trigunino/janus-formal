from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_janus_metric_pullback_phi_selector_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_metric_pullback_phi_selector_gate.json")
ETA2 = np.diag([-1.0, 1.0])
TOLERANCE = 1e-12


def metric_from_scales(a_time: float, a_space: float) -> np.ndarray:
    return np.diag([-a_time, a_space])


def solve_constant_diagonal_jacobian(metric_self: np.ndarray, metric_other: np.ndarray) -> np.ndarray:
    return np.diag(
        [
            np.sqrt(abs(metric_self[0, 0]) / abs(metric_other[0, 0])),
            np.sqrt(metric_self[1, 1] / metric_other[1, 1]),
        ]
    )


def boost_1p1(beta: float) -> np.ndarray:
    gamma = 1.0 / np.sqrt(1.0 - beta**2)
    return np.array([[gamma, beta * gamma], [beta * gamma, gamma]], dtype=float)


def metric_pullback_residual(jac: np.ndarray, metric_self: np.ndarray, metric_other: np.ndarray) -> np.ndarray:
    return metric_self - jac.T @ metric_other @ jac


def max_abs(matrix: np.ndarray) -> float:
    return float(np.max(np.abs(matrix)))


def conformal_curvature_sample(epsilon: float = 0.1, n: int = 256) -> dict:
    x = np.linspace(0.0, 2.0 * np.pi, n, endpoint=False)
    sigma = epsilon * np.cos(x)
    sigma_second = -epsilon * np.cos(x)
    curvature = -2.0 * np.exp(-2.0 * sigma) * sigma_second
    return {
        "epsilon": epsilon,
        "flat_other_curvature_max": 0.0,
        "self_curvature_max_abs": float(np.max(np.abs(curvature))),
        "curvature_mismatch_max_abs": float(np.max(np.abs(curvature))),
    }


def build_payload() -> dict:
    metric_other = ETA2.copy()
    metric_self = metric_from_scales(1.44, 0.64)
    selected_jacobian = solve_constant_diagonal_jacobian(metric_self, metric_other)
    selected_residual = metric_pullback_residual(selected_jacobian, metric_self, metric_other)
    boosted_jacobian = boost_1p1(0.2) @ selected_jacobian
    boosted_residual = metric_pullback_residual(boosted_jacobian, metric_self, metric_other)
    curvature = conformal_curvature_sample()
    selector_rows = [
        {
            "name": "isometry_pde",
            "formula": "C_mn[phi]=g_self_mn - d_m phi^a d_n phi^b g_other_ab(phi)=0",
            "meaning": "metric pullback equation selecting admissible phi candidates",
            "closed": True,
        },
        {
            "name": "jacobian_integrability",
            "formula": "J^a_m=d_m phi^a and d_m J^a_n-d_n J^a_m=0",
            "meaning": "a pointwise metric square-root must also be a true Jacobian",
            "closed": True,
        },
        {
            "name": "curvature_matching",
            "formula": "Riemann[g_self]=phi^*Riemann[g_other], hence scalar invariants must match",
            "meaning": "non-isometric metric branches cannot admit a pullback selector",
            "closed": True,
        },
        {
            "name": "boundary_killing_fix",
            "formula": "boundary/gauge conditions must remove translations and Lorentz/Killing freedom",
            "meaning": "metric pullback alone selects a family, not one physical phi",
            "closed": False,
        },
        {
            "name": "janus_source_selection",
            "formula": "Janus field/source equations must force the compatible isometry branch",
            "meaning": "without this, the soldered-L route stays conditional",
            "closed": False,
        },
    ]
    return {
        "description": "Metric-pullback phi selector derived from the soldered-L Lorentz condition.",
        "status": "metric-pullback-phi-selector-derived-conditional-no-general-source-closure",
        "depends_on": [
            "p0_janus_metric_pullback_compatibility_gate",
            "p0_janus_soldered_l_substitution_residual_gate",
            "p0_shared_phi_j_source_selection_gate",
            "p0_janus_source_isometry_selection_no_go",
        ],
        "selector_rows": selector_rows,
        "constant_metric_case": {
            "metric_self": metric_self.tolist(),
            "metric_other": metric_other.tolist(),
            "selected_jacobian": selected_jacobian.tolist(),
            "selected_phi": "phi^0=1.2 x^0+c^0, phi^1=0.8 x^1+c^1",
            "residual_max": max_abs(selected_residual),
            "selected": max_abs(selected_residual) < TOLERANCE,
        },
        "lorentz_family_case": {
            "beta": 0.2,
            "boosted_jacobian": boosted_jacobian.tolist(),
            "residual_max": max_abs(boosted_residual),
            "same_metric_residual_after_boost": max_abs(boosted_residual) < TOLERANCE,
            "shows_killing_lorentz_underselection": True,
        },
        "curvature_obstruction_case": curvature,
        "phi_selector_equation_derived": True,
        "constant_metric_phi_selected": max_abs(selected_residual) < TOLERANCE,
        "jacobian_integrability_required": True,
        "curvature_matching_required": True,
        "curvature_obstruction_detected": curvature["curvature_mismatch_max_abs"] > 1e-3,
        "lorentz_killing_family_underselected": max_abs(boosted_residual) < TOLERANCE,
        "boundary_gauge_required_for_unique_phi": True,
        "janus_source_selects_one_phi": False,
        "source_isometry_audit_artifact": "p0_janus_source_isometry_selection_no_go",
        "janus_source_selects_generic_metric_isometry": False,
        "pure_l_solder_generic_route_rejected": True,
        "metric_pullback_selection_generally_closed": False,
        "requires_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The phi selector is now explicit: solve the isometry PDE plus Jacobian curl "
            "and curvature matching. It selects phi on compatible metric branches up to "
            "Killing/boundary freedom. If Janus does not force local metric isometry, pure "
            "soldered-L is a conditional branch, not a general closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Metric Pullback Phi Selector Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Phi selector equation derived: {payload['phi_selector_equation_derived']}",
        f"Constant metric phi selected: {payload['constant_metric_phi_selected']}",
        f"Jacobian integrability required: {payload['jacobian_integrability_required']}",
        f"Curvature matching required: {payload['curvature_matching_required']}",
        f"Curvature obstruction detected: {payload['curvature_obstruction_detected']}",
        f"Lorentz/Killing family underselected: {payload['lorentz_killing_family_underselected']}",
        f"Boundary/gauge required for unique phi: {payload['boundary_gauge_required_for_unique_phi']}",
        f"Janus source selects one phi: {payload['janus_source_selects_one_phi']}",
        "Source isometry audit artifact: "
        f"`{payload['source_isometry_audit_artifact']}`",
        "Janus source selects generic metric isometry: "
        f"{payload['janus_source_selects_generic_metric_isometry']}",
        f"Pure L_solder generic route rejected: {payload['pure_l_solder_generic_route_rejected']}",
        f"Metric pullback selection generally closed: {payload['metric_pullback_selection_generally_closed']}",
        f"Requires observational fit: {payload['requires_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Selector Rows",
        "",
        "| name | formula | meaning | closed |",
        "|---|---|---|---:|",
    ]
    for row in payload["selector_rows"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['meaning']} | {row['closed']} |")
    const = payload["constant_metric_case"]
    family = payload["lorentz_family_case"]
    obstruction = payload["curvature_obstruction_case"]
    lines.extend(
        [
            "",
            "## Cases",
            "",
            f"- constant selected phi: `{const['selected_phi']}`; residual `{const['residual_max']:.12g}`",
            f"- boosted same-metric residual: `{family['residual_max']:.12g}`",
            f"- curvature mismatch max: `{obstruction['curvature_mismatch_max_abs']:.12g}`",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
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
