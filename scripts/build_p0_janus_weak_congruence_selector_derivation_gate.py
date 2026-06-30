from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_janus_weak_congruence_selector_derivation_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_weak_congruence_selector_derivation_gate.json")
ETA = np.diag([-1.0, 1.0, 1.0, 1.0])


def projector_perp_u(u: np.ndarray) -> np.ndarray:
    lowered = ETA @ u
    return np.eye(4) + np.outer(u, lowered)


def connection_force(connection_difference: np.ndarray, u: np.ndarray) -> np.ndarray:
    return np.einsum("mab,a,b->m", connection_difference, u, u)


def build_connection_difference() -> np.ndarray:
    c = np.zeros((4, 4, 4), dtype=float)
    c[0, 1, 1] = 0.30
    c[1, 0, 0] = 0.25
    c[2, 0, 0] = -0.15
    c[3, 2, 2] = 0.40
    return c


def build_payload() -> dict:
    u = np.array([1.0, 0.0, 0.0, 0.0])
    h = projector_perp_u(u)
    c = build_connection_difference()
    force = connection_force(c, u)
    projected_force = h @ force
    counterterm = -projected_force
    residual_after_selector = projected_force + counterterm
    full_connection_norm = float(np.max(np.abs(c)))
    selector_rows = [
        {
            "name": "weak_selector",
            "formula": "h^mu_nu C^nu_{alpha beta} u^alpha u^beta = 0",
            "meaning": "cancel only receiver-transverse dust acceleration",
            "closed": True,
        },
        {
            "name": "not_isometry",
            "formula": "C^mu_{alpha beta} need not vanish for transverse alpha,beta",
            "meaning": "two metrics may remain non-isometric",
            "closed": True,
        },
        {
            "name": "projected_action_target",
            "formula": "h E_phi/E_L = rho h C(u,u)",
            "meaning": "must still be derived from Janus/Stueckelberg action",
            "closed": False,
        },
        {
            "name": "mirror_target",
            "formula": "minus equation is inverse-map mirror of plus equation",
            "meaning": "prevents two independent gauge choices",
            "closed": False,
        },
        {
            "name": "non_dust_extension",
            "formula": "pressure/Pi add projected force and transport terms",
            "meaning": "dust-only selector is not general matter closure",
            "closed": False,
        },
    ]
    return {
        "description": "Weak congruence selector derivation gate after rejecting generic metric isometry.",
        "status": "weak-congruence-selector-derived-as-target-action-origin-open",
        "depends_on": [
            "p0_janus_source_isometry_selection_no_go",
            "p0_connection_force_weak_congruence_reduction",
            "p0_stueckelberg_weak_congruence_map_equation",
            "p0_projected_cuu_action_derivation_target",
        ],
        "selector_rows": selector_rows,
        "numeric_probe": {
            "u": u.tolist(),
            "projected_force": projected_force.tolist(),
            "selector_counterterm": counterterm.tolist(),
            "residual_after_selector": residual_after_selector.tolist(),
            "residual_norm": float(np.linalg.norm(residual_after_selector)),
            "full_connection_norm": full_connection_norm,
        },
        "weak_selector_equation_written": True,
        "dust_projected_residual_cancelled": float(np.linalg.norm(residual_after_selector)) < 1e-12,
        "full_connection_not_zero": full_connection_norm > 1e-3,
        "does_not_impose_metric_isometry": True,
        "generic_janus_not_excluded": True,
        "action_origin_closed": False,
        "mirror_consistency_closed": False,
        "pressure_pi_extension_closed": False,
        "requires_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The non-rustine replacement for full isometry is a weak congruence selector: "
            "cancel h C(u,u) for the transported dust congruence while leaving transverse "
            "connection/curvature free. This is the right target shape, but it is not final "
            "closure until derived from the Janus action and mirrored."
        ),
    }


def render_markdown(payload: dict) -> str:
    probe = payload["numeric_probe"]
    lines = [
        "# P0 Janus Weak Congruence Selector Derivation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Weak selector equation written: {payload['weak_selector_equation_written']}",
        f"Dust projected residual cancelled: {payload['dust_projected_residual_cancelled']}",
        f"Full connection not zero: {payload['full_connection_not_zero']}",
        f"Does not impose metric isometry: {payload['does_not_impose_metric_isometry']}",
        f"Generic Janus not excluded: {payload['generic_janus_not_excluded']}",
        f"Action origin closed: {payload['action_origin_closed']}",
        f"Mirror consistency closed: {payload['mirror_consistency_closed']}",
        f"Pressure/Pi extension closed: {payload['pressure_pi_extension_closed']}",
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
    lines.extend(
        [
            "",
            "## Numeric Probe",
            "",
            f"- projected force: `{probe['projected_force']}`",
            f"- selector counterterm: `{probe['selector_counterterm']}`",
            f"- residual norm: `{probe['residual_norm']:.12g}`",
            f"- full connection norm: `{probe['full_connection_norm']:.12g}`",
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
