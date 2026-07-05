from __future__ import annotations

import json
from pathlib import Path


INPUT_PATH = Path("outputs/active_z2_sigma/signed_cover_time_coordinate_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/active_time_coordinate_parity_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_signed_cover_time_parity_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_signed_cover_time_parity_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _build_output(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_curvature_fit_used",
        "observational_time_gauge_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")

    signed_time = payload.get("signed_cover_time_coordinate", {})
    required_true = [
        "coordinate_defined_on_S4_cover",
        "flrw_time_gauge_uses_this_coordinate",
        "z2_equivariant_time_coordinate_derived",
    ]
    for key in required_true:
        if signed_time.get(key) is not True:
            raise ValueError(f"signed_cover_time_coordinate.{key} must be true")

    pullback = signed_time.get("antipodal_pullback")
    if pullback == "plus_self":
        parity = "even"
    elif pullback == "minus_self":
        parity = "odd"
    else:
        raise ValueError("antipodal_pullback must be plus_self or minus_self")

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "observational_time_gauge_fit_used": False,
        "time_coordinate_parity": {
            "z2_equivariant_time_coordinate_derived": True,
            "antipodal_time_parity": parity,
            "source_antipodal_pullback": pullback,
        },
        "time_parity_policy": {
            "plus_self_pullback_gives": "even",
            "minus_self_pullback_gives": "odd",
            "time_gauge_not_fit": True,
        },
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    antipodal_time_parity = None
    if input_exists:
        try:
            output = _build_output(_load(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
            antipodal_time_parity = output["time_coordinate_parity"][
                "antipodal_time_parity"
            ]
        except Exception as exc:
            validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-signed-cover-time-parity-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "signed_cover_time_parity_rule_ready": True,
        "signed_cover_time_parity_input_written": output_written,
        "antipodal_time_parity": antipodal_time_parity,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "uses_observational_time_gauge_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "derive_signed_cover_time_coordinate_on_active_S4_cover",
            "write_outputs_active_z2_sigma_signed_cover_time_coordinate_inputs_json",
            "run_time_gauge_leaf_action_input_writer_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Signed-Cover Time Parity Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Rule ready: `{payload['signed_cover_time_parity_rule_ready']}`",
        f"Input written: `{payload['signed_cover_time_parity_input_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
