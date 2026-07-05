from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_counterterm_density_variation import (
    build_residual_tensors_from_local_density_action,
)


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
DENSITY_PATH = Path("outputs/active_z2_sigma/counterterm_local_density_action_inputs.json")
METRIC_OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_metric_residual_tensor_inputs.json")
EXTRINSIC_OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_extrinsic_residual_tensor_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_tensors_from_local_density_action.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_tensors_from_local_density_action.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(
    *,
    q_path: Path = Q_PATH,
    density_path: Path = DENSITY_PATH,
    metric_output_path: Path = METRIC_OUTPUT_PATH,
    extrinsic_output_path: Path = EXTRINSIC_OUTPUT_PATH,
) -> dict:
    input_exists = {
        "unit_intrinsic_metric_q_ab": q_path.exists(),
        "counterterm_local_density_action_inputs": density_path.exists(),
    }
    output_written = False
    validation_error = None
    diagnostic = None
    if all(input_exists.values()):
        try:
            result = build_residual_tensors_from_local_density_action(
                q_payload=_load(q_path),
                density_payload=_load(density_path),
            )
            metric_output_path.parent.mkdir(parents=True, exist_ok=True)
            metric_output_path.write_text(
                json.dumps(result["metric_payload"], indent=2),
                encoding="utf-8",
            )
            extrinsic_output_path.parent.mkdir(parents=True, exist_ok=True)
            extrinsic_output_path.write_text(
                json.dumps(result["extrinsic_payload"], indent=2),
                encoding="utf-8",
            )
            diagnostic = result["diagnostic"]
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-residual-tensors-from-local-density-action",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "metric_output_manifest": str(metric_output_path),
        "extrinsic_output_manifest": str(extrinsic_output_path),
        "residual_tensors_written": output_written,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "diagnostic": diagnostic,
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
        "# Janus Z2/Sigma Counterterm Residual Tensors From Local Density Action",
        "",
        f"Residual tensors written: `{payload['residual_tensors_written']}`",
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
