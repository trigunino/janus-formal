from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_global_regularity import (
    load_global_regular_component_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/global_regular_freg_components.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_solver_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_solver_gate.json")


def build_payload(*, input_path: Path = INPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-global-regular-freg-solver-gate",
            "active_core": "Z2_tunnel_Sigma",
            "input_manifest": str(input_path),
            "input_exists": False,
            "F_reg_value_ready": False,
            "R_Sigma_over_ell_collar_selected": False,
            "full_no_fit_prediction_ready": False,
            "gate_passed": False,
            "primary_blocker": "global_regular_freg_components_json",
            "next_required": [
                "write active normal-frame holonomy defect over lambda_grid",
                "write active collar endpoint mismatch over lambda_grid",
                "write active junction/Bianchi defect over lambda_grid",
            ],
        }
    validation_error = None
    solved = None
    try:
        solved = load_global_regular_component_payload(input_path)
    except Exception as exc:
        validation_error = str(exc)
    selected = bool(solved and solved["R_Sigma_over_ell_collar_selected"])
    return {
        "status": "janus-z2-sigma-global-regular-freg-solver-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "input_exists": True,
        "F_reg_value_ready": solved is not None,
        "R_Sigma_over_ell_collar_selected": selected,
        "regularity_roots": [] if solved is None else solved["regularity_roots"],
        "F_reg_min": None if solved is None else solved["F_reg_min"],
        "full_no_fit_prediction_ready": False,
        "gate_passed": selected,
        "primary_blocker": "none"
        if selected
        else "unique_global_regular_root_not_found",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Global Regular F_reg Solver Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"F_reg value ready: `{payload['F_reg_value_ready']}`",
        f"Ratio selected: `{payload['R_Sigma_over_ell_collar_selected']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
    ]
    if payload.get("regularity_roots"):
        lines.append(f"Regularity roots: `{payload['regularity_roots']}`")
    if payload.get("validation_error"):
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
