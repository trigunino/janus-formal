from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_cover/master_action_projection_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_minimal_projection_inputs.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_minimal_projection_inputs.json")


def build_payload(output_path: Path = OUTPUT_PATH) -> dict:
    manifest = {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "explicit_master_action_projection",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "two_independent_actions_used": False,
        "full_no_fit_prediction_ready": False,
        "kappa_symbol": "kappa_J",
        "B_minus_to_plus": "B_minus_to_plus",
        "B_plus_to_minus": "B_plus_to_minus",
        "Sigma_plus_boundary_source": "J_Sigma_plus",
        "Sigma_minus_boundary_source": "J_Sigma_minus",
        "self_sector_orientation_sign": 1,
        "cross_sector_orientation_sign": -1,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-cover-minimal-projection-inputs",
        "output_path": str(output_path),
        "active_core": "JanusZ2CoverMasterAction",
        "writes_active_manifest": True,
        "manifest_source": "symbolic_master_action_projection_not_observational",
        "rho_eff_shortcut_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Cover Minimal Projection Inputs",
                "",
                f"Output path: `{payload['output_path']}`",
                f"Writes active manifest: `{payload['writes_active_manifest']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
