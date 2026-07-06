from __future__ import annotations

import json
from pathlib import Path


COVER_INPUT_PATH = Path("outputs/active_z2_cover/master_action_projection_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_absolute_scale_descent_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_absolute_scale_descent_gate.json")


def _read_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(*, cover_input_path: Path = COVER_INPUT_PATH) -> dict:
    cover = _read_json(cover_input_path) or {}
    closure = {
        "cover_master_action_manifest_present": bool(cover),
        "single_cover_action_declared": cover.get("active_core") == "JanusZ2CoverMasterAction",
        "projective_projection_declared": cover.get("source") == "explicit_master_action_projection",
        "dimensionful_kappa_or_length_value_available": False,
        "cover_metric_radius_value_available": False,
        "cover_to_sigma_length_descent_map_available": False,
        "absolute_RSigma_from_cover_ready": False,
    }
    return {
        "status": "janus-z2-cover-absolute-scale-descent-gate",
        "active_core": "JanusZ2CoverMasterAction",
        "question": "Can the covering-level Janus action derive the absolute Sigma tunnel scale?",
        "result": (
            "Not with the current cover data. The cover gives symbolic projection "
            "structure and orientation signs, but no dimensionful cover radius, "
            "length parameter, or numeric kappa-to-length normalization. Therefore "
            "the homothety degeneracy descends unchanged to Sigma."
        ),
        "cover_inputs": {
            "manifest": str(cover_input_path),
            "kappa_symbol": cover.get("kappa_symbol"),
            "sigma_plus_boundary_source": cover.get("Sigma_plus_boundary_source"),
            "sigma_minus_boundary_source": cover.get("Sigma_minus_boundary_source"),
        },
        "closure": closure,
        "absolute_scale_can_descend_from_cover": all(closure.values()),
        "descent_rule_needed": (
            "R_Sigma = F[g_cover, action constants, boundary state] with F carrying "
            "physical length dimension."
        ),
        "allowed_now": [
            "orientation_sign_descent",
            "measure_transport_descent",
            "symbolic_kappa_J_accounting",
            "scale_free_RSigma_over_ell_collar_descent",
        ],
        "needed_to_close": [
            "dimensionful cover metric radius or collar length",
            "action-derived kappa_J value plus a length-setting state/charge",
            "cover boundary condition that fixes homothety",
            "explicit descent map from cover length to Sigma R_Sigma",
        ],
        "forbidden_shortcuts": [
            "do_not_treat_kappa_symbol_as_numeric_scale",
            "do_not_set_cover_radius_to_one_as_physical_length",
            "do_not_import_observational_H0_as_cover_scale",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Cover Absolute Scale Descent Gate",
        "",
        payload["result"],
        "",
        f"Absolute scale can descend from cover: `{payload['absolute_scale_can_descend_from_cover']}`",
        "",
        "## Needed To Close",
    ]
    lines.extend(f"- `{item}`" for item in payload["needed_to_close"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
