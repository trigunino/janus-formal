from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.weakfield_geometry import (
    dlog_weakfield_b4vol_1p1,
    periodic_derivative_1d,
    weakfield_b4vol_1p1,
)


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_b4vol_product_rule_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_b4vol_product_rule_probe.json")


def build_payload() -> dict:
    n = 64
    box = 2.0 * np.pi
    x = np.arange(n) * box / n
    phi = 1e-6 * np.cos(x)
    psi = 0.25e-6 * np.cos(x)
    exact = dlog_weakfield_b4vol_1p1(phi, psi, box)
    linear_target = periodic_derivative_1d(phi - psi, box)
    b4vol = weakfield_b4vol_1p1(phi, psi)
    metrics = {
        "max_abs_dlogb4vol_minus_d_phi_minus_psi": float(np.max(np.abs(exact - linear_target))),
        "max_abs_dlogb4vol": float(np.max(np.abs(exact))),
        "min_b4vol_1p1": float(np.min(b4vol)),
        "max_b4vol_1p1": float(np.max(b4vol)),
    }
    return {
        "description": "Diagnostic weak-field D log B4vol product-rule probe.",
        "status": "weakfield-b4vol-product-rule-probe-diagnostic",
        "depends_on": [
            "p0_janus_phase_space_b4vol_measure_gate",
            "p0_janus_weakfield_metric_force_probe",
        ],
        "metrics": metrics,
        "linear_product_rule_matches": metrics["max_abs_dlogb4vol_minus_d_phi_minus_psi"] < 2e-12,
        "b4vol_1p1_computed": True,
        "b4vol_source_law_derived": False,
        "qdet_absorbed": False,
        "diagnostic_only": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": (
            "This checks only the 1+1 weak-field determinant product rule. "
            "It does not derive the Janus 4D B4vol source law or Q_det convention."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field B4vol Product Rule Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Linear product rule matches: {payload['linear_product_rule_matches']}",
        f"B4vol 1+1 computed: {payload['b4vol_1p1_computed']}",
        f"B4vol source law derived: {payload['b4vol_source_law_derived']}",
        f"Q_det absorbed: {payload['qdet_absorbed']}",
        f"Diagnostic only: {payload['diagnostic_only']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Metrics",
        "",
        "| metric | value |",
        "|---|---:|",
    ]
    for name, value in payload["metrics"].items():
        lines.append(f"| {name} | {value:.6g} |")
    lines.extend(["", f"Boundary: {payload['boundary']}", ""])
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
