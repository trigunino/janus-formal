from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_no_extension_charge_normalization_no_go_gate import (
    build_payload as build_charge_no_go_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_rsigma_over_ell_collar_from_projective_stereographic import (
    build_payload as write_ratio_payload,
)


OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/effective_partial_closure_from_projective_ratio.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_partial_closure_from_projective_ratio.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_partial_closure_from_projective_ratio.json"
)


def build_payload(output_path: Path = OUTPUT_PATH) -> dict:
    ratio_payload = write_ratio_payload()
    charge_no_go = build_charge_no_go_payload()
    manifest = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "partial_effective_closure_from_projective_geometry",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "partial_effective_closure_ready": True,
        "effective_closure_ready": False,
        "derived_effective_initial_data": {
            "R_Sigma_over_ell_collar_Z2Sigma": ratio_payload[
                "R_Sigma_over_ell_collar"
            ],
        },
        "open_effective_initial_data": [
            "projected_baryon_number_charge_Z2Sigma",
        ],
        "blocked_downstream": [
            "effective_closure_inputs_json",
            "scale_free_BAO_primitive",
            "full_no_fit_prediction",
        ],
        "charge_blocker": charge_no_go["primary_blocker"],
        "provenance": {
            "R_Sigma_over_ell_collar_Z2Sigma": (
                "S^n antipodal stereographic radius inversion fixed point"
            ),
            "projected_baryon_number_charge_Z2Sigma": "not_derived_no_extension_no_go",
        },
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-sigma-effective-partial-closure-from-projective-ratio",
        "active_core": "Z2_tunnel_Sigma",
        "output_manifest": str(output_path),
        "output_written": True,
        "partial_effective_closure_ready": True,
        "effective_closure_ready": False,
        "R_Sigma_over_ell_collar_Z2Sigma": ratio_payload[
            "R_Sigma_over_ell_collar"
        ],
        "projected_baryon_number_charge_Z2Sigma_ready": False,
        "primary_blocker": charge_no_go["primary_blocker"],
        "next_required": [
            "derive projected_baryon_number_charge_Z2Sigma from state/Noether data",
            "or keep BAO/plasma sectors blocked",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Effective Partial Closure From Projective Ratio",
        "",
        f"Output written: `{payload['output_written']}`",
        f"Partial effective closure ready: `{payload['partial_effective_closure_ready']}`",
        f"Effective closure ready: `{payload['effective_closure_ready']}`",
        f"R_Sigma / ell_collar: `{payload['R_Sigma_over_ell_collar_Z2Sigma']}`",
        f"Charge ready: `{payload['projected_baryon_number_charge_Z2Sigma_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
