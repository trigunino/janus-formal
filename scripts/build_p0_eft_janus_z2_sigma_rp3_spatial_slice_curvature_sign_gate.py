from __future__ import annotations

import json
from pathlib import Path


INPUT_PATH = Path("outputs/active_z2_sigma/rp3_spatial_slice_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rp3_spatial_slice_curvature_sign_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rp3_spatial_slice_curvature_sign_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    for token in ["planck", "lcdm", "lambda-cdm", "lambda cdm", "z4", "fit"]:
        if token in lowered:
            raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def _build_sign(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    topology = payload.get("spatial_topology", {})
    if topology.get("cover_spatial_slice") != "S3":
        raise ValueError("cover_spatial_slice must be S3")
    if topology.get("quotient_spatial_slice") != "RP3":
        raise ValueError("quotient_spatial_slice must be RP3")
    if topology.get("antipodal_Z2_quotient") is not True:
        raise ValueError("antipodal_Z2_quotient must be true")
    provenance = payload.get("topology_provenance", {})
    rp3_provenance = _clean_source(
        provenance.get("quotient_spatial_slice", ""),
        "quotient_spatial_slice",
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {"k_Z2Sigma": 1},
        "scalar_provenance": {
            "k_Z2Sigma": f"active_RP3_spatial_slice_positive_curvature:({rp3_provenance})"
        },
        "sign_policy": {
            "topology_alone_used": False,
            "active_spatial_slice_RP3_used": True,
            "curvature_radius_still_required": True,
            "omega_k_not_computed_here": True,
        },
    }


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    sign_value = None
    if input_exists:
        try:
            output = _build_sign(_load(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            sign_value = output["scalars"]["k_Z2Sigma"]
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rp3-spatial-slice-curvature-sign-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "rp3_spatial_slice_to_k_plus_one_rule_ready": True,
        "curvature_sign_input_written": output_written,
        "topology_alone_fixes_numeric_omega_k": False,
        "curvature_radius_still_required": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "k_Z2Sigma_value": sign_value,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "derive_active_FLRW_spatial_slice_is_RP3",
            "write_outputs_active_z2_sigma_rp3_spatial_slice_inputs_json",
            "derive_active_R_curv_Z2Sigma_for_omega_k_and_volume",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma RP3 Spatial Slice Curvature Sign Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Rule ready: `{payload['rp3_spatial_slice_to_k_plus_one_rule_ready']}`",
        f"Sign input written: `{payload['curvature_sign_input_written']}`",
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
