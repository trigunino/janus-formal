from __future__ import annotations

from pathlib import Path
import json

import numpy as np

try:
    from scripts.build_kids1000_janus_holst_value_slip_kernel_target import build_payload as build_target_payload
except ModuleNotFoundError:
    from build_kids1000_janus_holst_value_slip_kernel_target import build_payload as build_target_payload

from janus_lab.value_slip import derivative_slip_source_shape, scaffold_status, sigma_from_mu_and_eta_slip


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_value_slip_scaffold.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_value_slip_scaffold.json")


def build_payload() -> dict:
    target = build_target_payload()
    k = np.asarray([0.01, 0.1, 1.0])
    a = np.asarray([0.7, 0.85, 1.0])
    derivative_source = derivative_slip_source_shape(k, a, omega_t=np.asarray([0.01]), chi_x=np.asarray([0.2]))
    eta_placeholder = np.zeros_like(derivative_source)
    sigma_placeholder = sigma_from_mu_and_eta_slip(np.ones_like(eta_placeholder), eta_placeholder)
    status = scaffold_status(green_kernel_computed=False, provenance="symbolic_scaffold")
    return {
        "description": "Non-fit value-slip code scaffold for the KiDS-1000 Janus-Holst lensing path.",
        "status": "value-slip-scaffold-not-closed",
        "target_status": target["status"],
        "sample_grid": {"k": [float(value) for value in k], "a": [float(value) for value in a]},
        "sample_derivative_source": [float(value) for value in derivative_source],
        "sigma_feed_formula": target["target_operator"]["must_feed"],
        "sigma_placeholder_with_eta_zero": [float(value) for value in sigma_placeholder],
        "scaffold": status,
        "green_kernel_computed": False,
        "uses_kids_residuals": False,
        "uses_delta_z": False,
        "uses_bin_factors": False,
        "prediction_ready": False,
        "blocked_reason": "Green kernel not computed; only derivative-source and Sigma feed interface are encoded.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Value-Slip Scaffold",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Target status: `{payload['target_status']}`",
        f"Green kernel computed: `{payload['green_kernel_computed']}`",
        f"Uses KiDS residuals: `{payload['uses_kids_residuals']}`",
        f"Uses delta_z: `{payload['uses_delta_z']}`",
        f"Uses bin factors: `{payload['uses_bin_factors']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Interface",
        "",
        f"- Sigma feed: `{payload['sigma_feed_formula']}`",
        f"- scaffold status: `{payload['scaffold']['status']}`",
        "",
        "## Sample Diagnostic Grid",
        "",
        f"- k: `{payload['sample_grid']['k']}`",
        f"- a: `{payload['sample_grid']['a']}`",
        f"- derivative source shape: `{payload['sample_derivative_source']}`",
        f"- Sigma placeholder eta=0: `{payload['sigma_placeholder_with_eta_zero']}`",
        "",
        payload["blocked_reason"],
        "",
    ]
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
