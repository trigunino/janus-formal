from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_counterterm_lct_profile import (
    build_lct_profile_from_residual_contractions,
)


INPUT_PATH = Path("outputs/active_z2_sigma/counterterm_residual_scalar_contractions_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_lct_radial_profile.json")
IMMIRZI_PATH = Path("outputs/active_z2_sigma/counterterm_immirzi_residual_scalar_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_radial_profile_from_residual_contractions.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_radial_profile_from_residual_contractions.json"
)


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    immirzi_path: Path = IMMIRZI_PATH,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    profile = None
    if input_exists:
        try:
            source = json.loads(input_path.read_text(encoding="utf-8"))
            profile = build_lct_profile_from_residual_contractions(source)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(profile, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    next_required = []
    if not output_written:
        next_required = [
            "derive_or_supply_R_Sigma_values",
            "derive_R_h_ab_q_ab_from_active_boundary_variation",
            "derive_R_K_ab_q_ab_from_active_boundary_variation",
            "fix_L_ct_integration_constant_from_active_boundary_condition",
        ]
        if not immirzi_path.exists():
            next_required.insert(
                3, "derive_R_chi_partial_R_chi_or_active_Immirzi_boundary_condition"
            )
    return {
        "status": "janus-z2-sigma-counterterm-lct-radial-profile-from-residual-contractions",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "L_ct_profile_written": output_written,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "profile": profile,
        "primary_blocker": "none"
        if output_written
        else "counterterm_residual_scalar_contractions_inputs",
        "immirzi_scalar_contraction_exists": immirzi_path.exists(),
        "next_required": next_required,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm L_ct Profile From Residual Contractions",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['L_ct_profile_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
