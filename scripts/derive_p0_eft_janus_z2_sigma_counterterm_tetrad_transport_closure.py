from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_counterterm_tetrad_transport import (
    build_counterterm_tetrad_transport_closure,
)


UNIT_Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
TORSION_PATH = Path("outputs/active_z2_sigma/torsion_pullback_components_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_tetrad_transport_closure.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_transport_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_transport_closure.json")


def build_payload(
    *,
    unit_q_path: Path = UNIT_Q_PATH,
    torsion_path: Path = TORSION_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = unit_q_path.exists() and torsion_path.exists()
    output_written = False
    validation_error = None
    closure: dict | None = None
    if input_exists:
        try:
            unit_q = json.loads(unit_q_path.read_text(encoding="utf-8"))
            torsion = json.loads(torsion_path.read_text(encoding="utf-8"))
            closure = build_counterterm_tetrad_transport_closure(
                unit_q_payload=unit_q,
                torsion_payload=torsion,
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(closure, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)

    gate_passed = bool(output_written and closure and closure["counterterm_residual_channel"]["tetrad_residual_channel_closed"])
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-transport-closure",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifests": {
            "unit_q": str(unit_q_path),
            "torsion_pullback": str(torsion_path),
        },
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "output_written": output_written,
        "gate_passed": gate_passed,
        "validation_error": validation_error,
        "closure": closure or {},
        "next_required": []
        if gate_passed
        else ["provide active unit q and torsion pullback inputs"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    closure = payload["closure"]
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Transport Closure",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Output written: `{payload['output_written']}`",
    ]
    if closure:
        lines.extend(
            [
                "",
                "## Derived Local Collar Formulae",
                f"- `h_ab`: `{closure['metric_transport']['h_ab']}`",
                f"- `K_ab`: `{closure['extrinsic_curvature_transport']['K_ab']}`",
                f"- `K_trace`: `{closure['extrinsic_curvature_transport']['K_trace']}`",
                f"- `partial_R_K_trace`: `{closure['extrinsic_curvature_transport']['partial_R_K_trace']}`",
                f"- torsion pullback zero: `{closure['torsion_pullback_transport']['torsion_pullback_value_zero']}`",
            ]
        )
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
