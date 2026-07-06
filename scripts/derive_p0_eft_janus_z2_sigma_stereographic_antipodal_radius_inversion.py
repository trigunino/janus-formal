from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.projective_stereographic import (
    antipodal_stereographic_radius,
    reciprocal_radius_fixed_point,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_stereographic_antipodal_radius_inversion.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_stereographic_antipodal_radius_inversion.json"
)


def build_payload(sample_radii: tuple[float, ...] = (0.5, 1.0, 2.0)) -> dict:
    mapped = [antipodal_stereographic_radius(radius) for radius in sample_radii]
    fixed = reciprocal_radius_fixed_point()
    return {
        "status": "janus-z2-sigma-stereographic-antipodal-radius-inversion",
        "active_core": "Z2_tunnel_Sigma",
        "source": "projective_geometry_derivation",
        "extension_allowed": False,
        "geometry": "S^n antipodal map in stereographic coordinates",
        "stereographic_antipodal_map": "x -> -x/|x|^2",
        "radius_law": "r -> 1/r",
        "sample_radii": list(sample_radii),
        "mapped_radii": mapped,
        "fixed_point": fixed,
        "candidate_R_Sigma_over_ell_collar": fixed,
        "connects_to_reciprocal_collar_probe": True,
        "promotion_ready": False,
        "primary_blocker": "prove_active_tunnel_lambda_is_the_projective_stereographic_radius",
        "interpretation": (
            "The projective S^n/RP^n antipodal geometry naturally supplies the "
            "reciprocal radius law. If the active tunnel collar coordinate lambda "
            "is identified with this stereographic radius, then the regular fixed "
            "throat ratio is lambda=1."
        ),
        "next_required": [
            "derive_active_tunnel_collar_coordinate_as_stereographic_projective_radius",
            "then_import_radius_law_into_reciprocal_collar_probe",
            "then_emit_R_Sigma_solution_certificate_with_R_Sigma_over_ell_collar_1",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Stereographic Antipodal Radius Inversion",
        "",
        f"Radius law: `{payload['radius_law']}`",
        f"Fixed point: `{payload['fixed_point']}`",
        f"Promotion ready: `{payload['promotion_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
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
