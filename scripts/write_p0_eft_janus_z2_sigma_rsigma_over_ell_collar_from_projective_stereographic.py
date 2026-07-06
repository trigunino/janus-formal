from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_stereographic_antipodal_radius_inversion import (
    build_payload as build_stereographic_payload,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_over_ell_collar_solution.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_over_ell_collar_from_projective_stereographic.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_over_ell_collar_from_projective_stereographic.json"
)


def build_payload(output_path: Path = OUTPUT_PATH) -> dict:
    stereographic = build_stereographic_payload()
    ratio = stereographic["candidate_R_Sigma_over_ell_collar"]
    manifest = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "projective_geometry_derivation",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "R_Sigma_over_ell_collar": ratio,
        "ratio_law": "lambda -> 1/lambda fixed point",
        "lambda_definition": "lambda = R_Sigma / ell_collar",
        "projective_coordinate_gauge": "stereographic_antipodal_radius",
        "absolute_ell_collar_fixed": False,
        "absolute_R_Sigma_fixed": False,
        "ratio_solution_ready": True,
        "full_R_Sigma_solution_certificate_ready": False,
        "provenance": "S^n antipodal stereographic map x -> -x/|x|^2 implies lambda -> 1/lambda",
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-sigma-rsigma-over-ell-collar-from-projective-stereographic",
        "active_core": "Z2_tunnel_Sigma",
        "source": "projective_geometry_derivation",
        "output_manifest": str(output_path),
        "output_written": True,
        "R_Sigma_over_ell_collar": ratio,
        "ratio_solution_ready": True,
        "full_R_Sigma_solution_certificate_ready": False,
        "primary_blocker": "absolute_ell_collar_scale_not_fixed",
        "next_required": [
            "derive_absolute_ell_collar_scale_or_keep_scale_free_branch",
            "feed_ratio_solution_to_effective_Z2Sigma_initial_data_only_if_scale_free",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma R_Sigma / ell_collar From Projective Stereographic Geometry",
        "",
        f"Output written: `{payload['output_written']}`",
        f"Ratio: `{payload['R_Sigma_over_ell_collar']}`",
        f"Full R_Sigma certificate ready: `{payload['full_R_Sigma_solution_certificate_ready']}`",
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
