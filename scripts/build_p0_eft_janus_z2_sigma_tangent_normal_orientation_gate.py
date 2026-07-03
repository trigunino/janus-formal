from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tangent_normal_orientation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tangent_normal_orientation_gate.json")


def build_payload() -> dict:
    declared = {
        "thin_shell_normal_bibliography_checked": True,
        "Sigma_embedding_declared": True,
        "active_embedding_from_radius_gate_declared": True,
        "tangent_frame_formula_declared": True,
        "unit_normal_formula_declared": True,
        "orthogonality_normalization_declared": True,
        "Z2_normal_orientation_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "active_Sigma_embedding_ready": False,
        "tangent_frames_of_a_ready": False,
        "unit_normals_of_a_ready": False,
        "Z2_orientation_sign_fixed": False,
        "tangent_normal_orientation_ready": False,
    }
    return {
        "status": "janus-z2-sigma-tangent-normal-orientation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel 1966 singular hypersurfaces/thin shells",
            "Poisson thin-shell hypersurface normal conventions",
            "Barrabes-Israel thin-shell/null-shell orientation conventions",
            "active tunnel embedding from radius gate",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies tangent frames, unit normals, "
            "orthogonality/normalization and orientation conventions. It does not "
            "supply the active Janus resolved-tunnel embedding X_+(a), X_-(a)."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "embedding": "X_pm^mu(y^a): Sigma -> M_pm",
            "tangent": "e_a^mu = partial_a X_pm^mu",
            "normal_orthogonality": "n_pm_mu e_a^mu = 0",
            "normal_normalization": "n_pm_mu n_pm^mu = epsilon_pm",
            "z2_orientation": "n_- is fixed by the Z2 reversal/oriented gluing convention relative to n_+",
        },
        "tangent_normal_orientation_ledger_declared": all(declared.values()),
        "tangent_normal_orientation_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_active_tunnel_embedding_of_a_gate",
            "pass_active_tunnel_embedding_from_radius_gate",
            "derive_tangent_frames_from_X_plus_minus_of_a",
            "solve_unit_normals_from_orthogonality_and_normalization",
            "fix_Z2_normal_orientation_sign_from_projective_tunnel_gluing",
            "feed_frames_to_coframe_connection_pullback_gate",
            "feed_frames_to_extrinsic_curvature_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Tangent Normal Orientation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['tangent_normal_orientation_ledger_declared']}`",
        f"Orientation ready: `{payload['tangent_normal_orientation_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
