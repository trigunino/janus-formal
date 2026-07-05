from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_projective_tunnel_interface import (
    build_payload as build_projective_tunnel_payload,
)
from janus_lab.z2_sigma_embedding_geometry_manifest import (
    load_active_z2sigma_embedding_geometry_manifest,
)
from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_frame_bundle_gate import (
    build_payload as build_frame_bundle_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_tangent_normal_orientation_gate import (
    build_payload as build_tangent_normal_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flux_projection_domain_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flux_projection_domain_gate.json")
EMBEDDING_MANIFEST_PATH = Path("outputs/active_z2_sigma/active_tunnel_embedding_geometry_inputs.json")


def _embedding_manifest_status(path: Path = EMBEDDING_MANIFEST_PATH) -> dict:
    exists = path.exists()
    valid = False
    validation_error = None
    if exists:
        try:
            load_active_z2sigma_embedding_geometry_manifest(path)
            valid = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "path": str(path),
        "exists": exists,
        "valid": valid,
        "validation_error": validation_error,
    }


def build_payload() -> dict:
    tunnel = build_projective_tunnel_payload()
    frame_bundle = build_frame_bundle_payload()
    embedding = build_active_embedding_payload()
    embedding_manifest = _embedding_manifest_status()
    tangent_normal = build_tangent_normal_payload()
    declared = {
        "thin_shell_flux_domain_bibliography_checked": True,
        "projective_tunnel_sigma_declared": tunnel["projective_tunnel_interface"][
            "tunnel_throat_sigma_defined"
        ],
        "z2_coorientation_sign_declared": tangent_normal["closure"][
            "Z2_orientation_sign_fixed"
        ],
        "induced_metric_nondegeneracy_condition_declared": True,
        "frame_trace_transport_declared": True,
        "no_independent_frame_fit": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "coorientation_ready": all(
            [
                declared["projective_tunnel_sigma_declared"],
                declared["z2_coorientation_sign_declared"],
            ]
        ),
        "resolved_frame_bundle_ready": frame_bundle[
            "resolved_tunnel_frame_bundle_ready"
        ],
        "regular_embedding_ready": embedding["readiness"]["active_embedding_ready"],
        "embedding_geometry_manifest_valid": embedding_manifest["valid"],
        "induced_metric_nondegenerate_ready": False,
        "embedding_of_a_ready": embedding["readiness"]["X_plus_minus_of_a_ready"],
        "Sigma_tangents_ready": embedding["readiness"]["tangent_frames_ready"],
        "Sigma_normals_ready": embedding["readiness"]["unit_normals_ready"],
        "flux_projection_domain_ready": False,
    }
    closure["induced_metric_nondegenerate_ready"] = (
        closure["resolved_frame_bundle_ready"]
        and closure["regular_embedding_ready"]
        and closure["Sigma_tangents_ready"]
    )
    closure["flux_projection_domain_ready"] = (
        all(declared.values())
        and closure["coorientation_ready"]
        and closure["embedding_geometry_manifest_valid"]
        and closure["induced_metric_nondegenerate_ready"]
        and closure["Sigma_normals_ready"]
    )
    primary_blocker = (
        "none"
        if closure["flux_projection_domain_ready"]
        else frame_bundle.get("primary_blocker")
        or embedding.get("primary_blocker")
        or tangent_normal.get("primary_blocker")
        or "active_embedding_geometry_manifest"
    )
    return {
        "status": "janus-z2-sigma-flux-projection-domain-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell tangent/normal flux projection",
            "tubular neighborhood and collar gluing prerequisites",
            "frame bundle construction from a smooth tangent bundle",
        ],
        "bibliography_result": (
            "Thin-shell flux projection requires a cooriented Sigma, a nondegenerate "
            "induced metric, tangent traces and unit normals. The active projective "
            "tunnel supplies Sigma and the Z2 coorientation sign, but not the "
            "scale-factor embedding or frame traces."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "projective_tunnel": {
                "gate": tunnel["status"],
                "sigma_defined": tunnel["projective_tunnel_interface"][
                    "tunnel_throat_sigma_defined"
                ],
            },
            "frame_bundle": {
                "gate": frame_bundle["status"],
                "ready": frame_bundle["resolved_tunnel_frame_bundle_ready"],
                "closure": frame_bundle["closure"],
                "primary_blocker": frame_bundle.get("primary_blocker"),
            },
            "active_embedding": {
                "gate": embedding["status"],
                "ready": embedding["active_embedding_readiness_ready"],
                "readiness": embedding["readiness"],
                "primary_blocker": embedding.get("primary_blocker"),
            },
            "embedding_geometry_manifest": embedding_manifest,
            "tangent_normal": {
                "gate": tangent_normal["status"],
                "ready": tangent_normal["tangent_normal_orientation_ready"],
                "closure": tangent_normal["closure"],
                "primary_blocker": tangent_normal.get("primary_blocker"),
            },
        },
        "formula": {
            "flux_projection": "F_a^pm = T_munu^pm e_a^mu n_pm^nu",
            "domain_condition": "Sigma cooriented, h_ab nondegenerate, e_a and n_pm transported from active embedding",
        },
        "flux_projection_domain_ledger_declared": all(declared.values()),
        "flux_projection_domain_ready": closure["flux_projection_domain_ready"],
        "gate_passed": closure["flux_projection_domain_ready"],
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false" for key, ready in closure.items() if not ready
        ],
        "next_required": [
            "derive_resolved_tunnel_frame_bundle",
            "solve_R_Sigma_of_a_and_X_plus_minus_of_a",
            "derive_tangent_frames_and_unit_normals",
            "then_project_bulk_stress_or_test_transparency",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Flux Projection Domain Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['flux_projection_domain_ledger_declared']}`",
        f"Projection domain ready: `{payload['flux_projection_domain_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Current Frontier",
    ]
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
