from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_effective_closure import validate_effective_closure_payload


INPUT_PATH = Path("outputs/active_z2_sigma/effective_closure_inputs.json")
PARTIAL_PATH = Path(
    "outputs/active_z2_sigma/effective_partial_closure_from_projective_ratio.json"
)
OCCUPATION_PATH = Path("outputs/active_z2_sigma/projected_occupation_state_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_closure_input_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_closure_input_gate.json"
)


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    partial_path: Path = PARTIAL_PATH,
    occupation_path: Path = OCCUPATION_PATH,
) -> dict:
    input_exists = input_path.exists()
    partial_exists = partial_path.exists()
    occupation_exists = occupation_path.exists()
    validation_error = None
    effective = None
    if input_exists:
        try:
            effective = validate_effective_closure_payload(
                json.loads(input_path.read_text(encoding="utf-8"))
            )
        except Exception as exc:
            validation_error = str(exc)
    ready = effective is not None
    if ready:
        primary_blocker = "none"
        next_required = []
    elif partial_exists and not occupation_exists:
        primary_blocker = "projected_occupation_state_inputs_json"
        next_required = [
            "write outputs/active_z2_sigma/projected_occupation_state_inputs.json",
            "source must be explicit_state_initial_data",
            "then run write_p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation.py",
        ]
    else:
        primary_blocker = "effective_closure_inputs_json"
        next_required = [
            "write outputs/active_z2_sigma/effective_closure_inputs.json",
            "include only R_Sigma_over_ell_collar_Z2Sigma and projected_baryon_number_charge_Z2Sigma",
            "keep full_no_fit_prediction_ready false",
        ]
    return {
        "status": "janus-z2-sigma-effective-closure-input-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "input_exists": input_exists,
        "partial_projective_ratio_exists": partial_exists,
        "projected_occupation_state_input_exists": occupation_exists,
        "effective_closure_ready": ready,
        "full_no_fit_prediction_ready": False,
        "allowed_effective_parameters": [
            "R_Sigma_over_ell_collar_Z2Sigma",
            "projected_baryon_number_charge_Z2Sigma",
        ],
        "forbidden_inputs": [
            "compressed_planck_lcdm",
            "archived_z4",
            "observational_fit",
            "extra_sigma_density_without_declaration",
        ],
        "effective_initial_data": effective["effective_initial_data"] if ready else None,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "validation_error": validation_error,
        "next_required": next_required,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective Closure Input Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Effective closure ready: `{payload['effective_closure_ready']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
