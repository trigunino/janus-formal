from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_tunnel_embedding_of_a_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_active_tunnel_embedding_of_a_gate.json")


def build_payload() -> dict:
    declared = {
        "Janus_projective_tunnel_bibliography_checked": True,
        "thin_shell_embedding_bibliography_checked": True,
        "resolved_projective_tunnel_topology_declared": True,
        "tunnel_embedding_constraint_ledger_declared": True,
        "active_scale_factor_parameter_declared": True,
        "X_plus_of_a_declared": True,
        "X_minus_of_a_declared": True,
        "induced_metric_matching_of_a_declared": True,
        "Z2_equivariance_of_embedding_declared": True,
        "regular_throat_radius_of_a_declared": True,
        "embedding_from_radius_gate_declared": True,
    }
    derived = {
        "X_plus_minus_of_a_derived": False,
        "DeltaK_s_of_a_derived": False,
        "DeltaK_tau_of_a_derived": False,
    }
    return {
        "status": "janus-z2-sigma-active-tunnel-embedding-of-a-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Petit/Margnat/Zejli 2024, arXiv:2412.04644",
            "Israel/Lanczos thin-shell embedding formalism",
            "Singular hypersurfaces and thin shells in cosmology, arXiv:2402.09539",
            "active tunnel embedding from radius gate",
        ],
        "bibliography_result": (
            "Projective/tunnel topology and generic shell embedding machinery are available. "
            "No primary source gives active X_+(a), X_-(a) for the resolved Janus tunnel."
        ),
        "declared": declared,
        "derived": derived,
        "embedding_requirements": {
            "X_plus": "X_+^mu(a, xi^i): Sigma -> M_+",
            "X_minus": "X_-^mu(a, xi^i): Sigma -> M_-",
            "matching": "pullback(g_+) = pullback(g_-) = h_Sigma(a)",
            "Z2_equivariance": "deck transformation maps X_+(a) to X_-(a)",
            "regular_throat": "R_Sigma(a) finite and nonzero on the resolved tunnel",
        },
        "active_tunnel_embedding_problem_declared": all(declared.values()),
        "active_tunnel_embedding_of_a_closure_ready": all(declared.values())
        and all(derived.values()),
        "next_required": [
            "pass_tunnel_embedding_constraint_count_gate",
            "pass_active_tunnel_embedding_from_radius_gate",
            "derive_X_plus_of_a_and_X_minus_of_a_from_resolved_projective_tunnel_geometry",
            "derive_regular_throat_radius_RSigma_of_a",
            "compute_normals_and_K_ab_from_X_plus_minus_of_a",
            "reduce_to_DeltaK_s_of_a_and_DeltaK_tau_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Active Tunnel Embedding Of A Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Problem declared: `{payload['active_tunnel_embedding_problem_declared']}`",
        f"Closure ready: `{payload['active_tunnel_embedding_of_a_closure_ready']}`",
        "",
        "## Embedding Requirements",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["embedding_requirements"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
