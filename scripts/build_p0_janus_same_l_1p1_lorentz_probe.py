from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.vlasov_diagnostic import (
    gaussian_phase_space,
    lorentz_boost_1p1,
    lorentz_residual_1p1,
    minkowski_trace_1p1,
    stress_energy_1p1,
    transform_rank2_1p1,
)


REPORT_PATH = Path("outputs/reports/p0_janus_same_l_1p1_lorentz_probe.md")
JSON_PATH = Path("outputs/reports/p0_janus_same_l_1p1_lorentz_probe.json")


def build_payload() -> dict:
    x = (np.arange(16) + 0.5) / 16.0
    v = np.linspace(-0.8, 0.8, 16, endpoint=False)
    dv = v[1] - v[0]
    f = gaussian_phase_space(x, v, x0=0.45, sigma_x=0.1, sigma_v=0.25, box_size=1.0)
    boost = lorentz_boost_1p1(0.25)
    tensor = stress_energy_1p1(f, v, dv)
    transformed = transform_rank2_1p1(tensor, boost)
    trace_error = abs(minkowski_trace_1p1(transformed) - minkowski_trace_1p1(tensor))
    metrics = {
        "lorentz_residual": lorentz_residual_1p1(boost),
        "minkowski_trace_error": trace_error,
        "t00_initial": float(tensor[0, 0]),
        "t00_transformed": float(transformed[0, 0]),
    }
    return {
        "description": "Diagnostic 1+1 same-L Lorentz probe for kinetic stress transport.",
        "status": "same-l-1p1-lorentz-probe-diagnostic",
        "depends_on": ["p0_janus_same_l_transport_stack_gate"],
        "metrics": metrics,
        "lorentz_condition_passes": metrics["lorentz_residual"] < 1e-12,
        "same_l_used_for_tensor_transform": True,
        "dl_source_derived": False,
        "diagnostic_only": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "boundary": "This probe checks algebraic Lorentz transport only; it does not derive the Janus same-L or D L law.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Same-L 1+1 Lorentz Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lorentz condition passes: {payload['lorentz_condition_passes']}",
        f"Same L used for tensor transform: {payload['same_l_used_for_tensor_transform']}",
        f"D L source-derived: {payload['dl_source_derived']}",
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
