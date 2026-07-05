from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_counterterm_scalar_contractions import (
    build_residual_scalar_contractions,
)


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
RADIUS_PATH = Path("outputs/active_z2_sigma/rsigma_solution_certificate.json")
METRIC_PATH = Path("outputs/active_z2_sigma/counterterm_metric_residual_tensor_inputs.json")
EXTRINSIC_PATH = Path("outputs/active_z2_sigma/counterterm_extrinsic_residual_tensor_inputs.json")
IMMIRZI_PATH = Path("outputs/active_z2_sigma/counterterm_immirzi_residual_scalar_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_residual_scalar_contractions_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_scalar_contractions.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_scalar_contractions.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(
    *,
    q_path: Path = Q_PATH,
    radius_path: Path = RADIUS_PATH,
    metric_path: Path = METRIC_PATH,
    extrinsic_path: Path = EXTRINSIC_PATH,
    immirzi_path: Path = IMMIRZI_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    paths = {
        "unit_intrinsic_metric_q_ab": q_path,
        "R_Sigma_solution_certificate": radius_path,
        "metric_residual_tensor_R_h_ab": metric_path,
        "extrinsic_residual_tensor_R_K_ab": extrinsic_path,
        "immirzi_residual_scalar_R_chi": immirzi_path,
    }
    input_exists = {name: path.exists() for name, path in paths.items()}
    output_written = False
    validation_error = None
    contractions = None
    if all(input_exists.values()):
        try:
            contractions = build_residual_scalar_contractions(
                q_payload=_load(q_path),
                radius_payload=_load(radius_path),
                metric_payload=_load(metric_path),
                extrinsic_payload=_load(extrinsic_path),
                immirzi_payload=_load(immirzi_path),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(contractions, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-residual-scalar-contractions",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "residual_scalar_contractions_written": output_written,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "contractions": contractions,
        "primary_blocker": "none"
        if output_written
        else next((name for name, exists in input_exists.items() if not exists), "invalid_inputs"),
        "next_required": []
        if output_written
        else [
            name for name, exists in input_exists.items() if not exists
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Residual Scalar Contractions",
        "",
        f"Output written: `{payload['residual_scalar_contractions_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
