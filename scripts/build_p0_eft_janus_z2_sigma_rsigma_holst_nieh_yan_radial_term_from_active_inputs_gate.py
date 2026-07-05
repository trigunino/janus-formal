from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from janus_lab.z2_sigma_rsigma_radial_terms import (
    build_active_z2sigma_rsigma_radial_term_payload,
    write_active_z2sigma_rsigma_radial_term_manifest,
)


INPUT_PATH = Path("outputs/active_z2_sigma/holst_nieh_yan_radial_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_holst_nieh_yan_radial_term_from_active_inputs_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_holst_nieh_yan_radial_term_from_active_inputs_gate.json")


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Holst/Nieh-Yan active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Holst/Nieh-Yan source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    torsionless_zero_identity = payload.get("torsionless_Nieh_Yan_zero_identity_ready") is True
    required_keys = [
        "torsion_pullback_on_Sigma_ready",
        "FLRW_irreducible_torsion_pullback_ready",
        "holst_nieh_yan_radial_reduction_ready",
    ]
    if not torsionless_zero_identity:
        required_keys.append("Immirzi_radial_profile_ready")
    for key in required_keys:
        if payload.get(key) is not True:
            raise ValueError(f"{key} must be true")
    if payload.get("selected_radial_term") != "E_HolstNiehYan":
        raise ValueError("selected_radial_term must be E_HolstNiehYan")
    return payload


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            source = _load_input(input_path)
            term = build_active_z2sigma_rsigma_radial_term_payload(
                term_name="E_HolstNiehYan",
                a_grid=source["a_grid"],
                term_values=source["E_HolstNiehYan_values"],
                term_provenance=(
                    "active Holst/Nieh-Yan radial block from Sigma torsion pullback, "
                    "FLRW irreducible torsion split, and Immirzi radial profile"
                ),
            )
            write_active_z2sigma_rsigma_radial_term_manifest(output_path, term)
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rsigma-holst-nieh-yan-radial-term-from-active-inputs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "E_HolstNiehYan_from_active_inputs_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_holst_nieh_yan_radial_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_Sigma_torsion_pullback_from_active_Z2_Sigma_connection",
            "derive_FLRW_irreducible_torsion_pullback_on_Sigma",
            "derive_Immirzi_radial_profile_from_active_boundary_action",
            "reduce_Holst_Nieh_Yan_block_to_E_HolstNiehYan_values",
            "write_outputs_active_z2_sigma_holst_nieh_yan_radial_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Holst-Nieh-Yan Radial Term From Active Inputs Gate",
        "",
        f"Output written: `{payload['E_HolstNiehYan_from_active_inputs_written']}`",
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
