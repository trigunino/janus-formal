from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.vlasov_diagnostic import gaussian_phase_space, phase_space_mass_with_weight


REPORT_PATH = Path("outputs/reports/p0_janus_phase_space_measure_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_phase_space_measure_probe.json")


def build_payload() -> dict:
    nx = 32
    nv = 16
    box_size = 1.0
    x = (np.arange(nx) + 0.5) * box_size / nx
    v = np.linspace(-1.0, 1.0, nv, endpoint=False)
    dx = box_size / nx
    dv = v[1] - v[0]
    f = gaussian_phase_space(x, v, x0=0.4, sigma_x=0.08, sigma_v=0.25, box_size=box_size)
    b4vol = 1.0 + 0.05 * np.sin(2.0 * np.pi * x)
    qdet = 1.0 + 0.03 * np.cos(2.0 * np.pi * x)
    metrics = {
        "mass_unweighted": phase_space_mass_with_weight(f, dx, dv),
        "mass_with_b4vol": phase_space_mass_with_weight(f, dx, dv, b4vol),
        "mass_with_qdet_diagnostic_only": phase_space_mass_with_weight(f, dx, dv, qdet),
        "max_abs_b4vol_minus_one": float(np.max(np.abs(b4vol - 1.0))),
        "max_abs_qdet_minus_one": float(np.max(np.abs(qdet - 1.0))),
    }
    return {
        "description": "Diagnostic phase-space measure probe keeping B4vol and Q_det separate.",
        "status": "phase-space-measure-probe-diagnostic",
        "depends_on": ["p0_janus_phase_space_b4vol_measure_gate"],
        "metrics": metrics,
        "b4vol_weight_explicit": True,
        "qdet_kept_separate": True,
        "qdet_used_as_physical_measure": False,
        "diagnostic_only": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": "This probe checks weighted bookkeeping only; it does not derive B4vol or Q_det from Janus source equations.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Phase-Space Measure Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B4vol weight explicit: {payload['b4vol_weight_explicit']}",
        f"Q_det kept separate: {payload['qdet_kept_separate']}",
        f"Q_det used as physical measure: {payload['qdet_used_as_physical_measure']}",
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
