from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_embedding_extrinsic_curvature_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tunnel_embedding_extrinsic_curvature_gate.json")


def build_payload() -> dict:
    structural = {
        "thin_shell_embedding_bibliography_checked": True,
        "Sigma_embeddings_declared": True,
        "tangent_frames_declared": True,
        "unit_normals_declared": True,
        "induced_metric_matching_declared": True,
        "extrinsic_curvature_definition_ready": True,
        "Z2_normal_orientation_applied": True,
        "DeltaK_s_from_K_plus_minus_ready": True,
        "DeltaK_tau_from_K_plus_minus_ready": True,
    }
    scale_factor = {
        "active_tunnel_embedding_of_a_problem_declared": True,
        "tunnel_embedding_functions_of_a_ready": False,
        "DeltaK_s_of_a_ready": False,
        "DeltaK_tau_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-tunnel-embedding-extrinsic-curvature-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell junction formalism",
            "Poisson thin-shell/extrinsic-curvature convention",
            "Singular hypersurfaces and thin shells in cosmology, arXiv:2402.09539",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies K_ab from embeddings, tangents and normals. "
            "The active Janus Z2/Sigma tunnel embedding functions X_+(a), X_-(a) are not provided."
        ),
        "structural": structural,
        "scale_factor": scale_factor,
        "definitions": {
            "embedding": "X_pm^mu(y^a): Sigma -> M_pm",
            "tangent": "e_a^mu = partial X_pm^mu / partial y^a",
            "normal": "n_pm_mu e_a^mu = 0, n_pm_mu n_pm^mu = eps_pm",
            "extrinsic_curvature": "K_ab^pm = e_a^mu e_b^nu nabla_mu n_nu^pm",
            "DeltaK_s": "Z2-oriented spatial trace jump of K_ab",
            "DeltaK_tau": "Z2-oriented time-time jump of K_ab",
        },
        "extrinsic_curvature_structural_closure_ready": all(structural.values()),
        "extrinsic_curvature_scale_factor_closure_ready": all(structural.values())
        and all(scale_factor.values()),
        "next_required": [
            "pass_active_tunnel_embedding_of_a_gate",
            "compute_unit_normals_from_active_tunnel_embedding",
            "reduce_K_ab_plus_minus_to_DeltaK_s_of_a_and_DeltaK_tau_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Tunnel Embedding Extrinsic Curvature Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Structural closure ready: `{payload['extrinsic_curvature_structural_closure_ready']}`",
        f"Scale-factor closure ready: `{payload['extrinsic_curvature_scale_factor_closure_ready']}`",
        "",
        "## Definitions",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["definitions"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
