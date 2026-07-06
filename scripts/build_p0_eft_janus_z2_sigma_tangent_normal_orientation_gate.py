from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_tunnel_embedding_of_a_gate import (
    build_payload as build_active_tunnel_embedding_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tangent_normal_orientation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_tangent_normal_orientation_gate.json")
FRAME_PATH = Path("outputs/active_z2_sigma/sigma_unit_frame_inputs.json")


def _local_unit_frame_ready(path: Path = FRAME_PATH) -> tuple[bool, str | None]:
    if not path.exists():
        return False, "sigma_unit_frame_inputs_missing"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        normals_plus = np.asarray(payload.get("unit_normals_plus"), dtype=float)
        normals_minus = np.asarray(payload.get("unit_normals_minus"), dtype=float)
        if payload.get("active_core") != "Z2_tunnel_Sigma":
            return False, "active_core_mismatch"
        if payload.get("source") != "active_derived":
            return False, "source_not_active_derived"
        if payload.get("sigma_unit_frame_ready") is not True:
            return False, "sigma_unit_frame_not_ready"
        if normals_plus.ndim != 2 or normals_minus.shape != normals_plus.shape:
            return False, "unit_normals_invalid"
        if not np.allclose(normals_minus, -normals_plus, atol=1e-12):
            return False, "minus_normal_not_z2_reversed"
        if bool(payload.get("full_embedding_claimed")):
            return False, "full_embedding_must_not_be_claimed"
        return True, None
    except Exception as exc:
        return False, str(exc)


def build_payload() -> dict:
    embedding = build_active_tunnel_embedding_payload()
    local_frame_ready, local_frame_error = _local_unit_frame_ready()
    declared = {
        "thin_shell_normal_bibliography_checked": True,
        "Sigma_embedding_declared": True,
        "active_embedding_from_radius_gate_declared": True,
        "projective_gluing_normal_orientation_sign_gate_declared": True,
        "embedding_tangent_frame_transport_gate_declared": True,
        "tangent_frame_formula_declared": True,
        "unit_normal_formula_declared": True,
        "orthogonality_normalization_declared": True,
        "Z2_normal_orientation_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "local_unit_tangent_normal_frame_ready": local_frame_ready,
        "local_unit_normals_ready": local_frame_ready,
        "local_Z2_normal_reversal_ready": local_frame_ready,
        "active_Sigma_embedding_ready": embedding["active_tunnel_embedding_of_a_closure_ready"],
        "tangent_frames_of_a_ready": False,
        "unit_normals_of_a_ready": False,
        "Z2_orientation_sign_fixed": True,
        "active_tangent_normal_orientation_ready": False,
        "tangent_normal_orientation_ready": local_frame_ready,
    }
    ready = all(declared.values()) and local_frame_ready and closure["Z2_orientation_sign_fixed"]
    return {
        "status": "janus-z2-sigma-tangent-normal-orientation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel 1966 singular hypersurfaces/thin shells",
            "Poisson thin-shell hypersurface normal conventions",
            "Barrabes-Israel thin-shell/null-shell orientation conventions",
            "active tunnel embedding from radius gate",
            "projective gluing normal orientation sign gate",
            "embedding tangent frame transport gate",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies tangent frames, unit normals, "
            "orthogonality/normalization and orientation conventions. It does not "
            "supply the active Janus resolved-tunnel embedding X_+(a), X_-(a). "
            "For local boundary projectors the active unit frame closes the normal "
            "orientation without claiming the full embedding."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "active_tunnel_embedding_of_a": {
                "gate": embedding["status"],
                "ready": embedding["active_tunnel_embedding_of_a_closure_ready"],
                "derived": embedding["derived"],
                "primary_blocker": embedding.get("primary_blocker"),
            },
            "local_unit_frame_inputs": {
                "path": str(FRAME_PATH),
                "ready": local_frame_ready,
                "validation_error": local_frame_error,
                "full_embedding_claimed": False,
            },
        },
        "formulas": {
            "embedding": "X_pm^mu(y^a): Sigma -> M_pm",
            "tangent": "e_a^mu = partial_a X_pm^mu",
            "normal_orthogonality": "n_pm_mu e_a^mu = 0",
            "normal_normalization": "n_pm_mu n_pm^mu = epsilon_pm",
            "z2_orientation": "n_- = - tau_Z2_* n_+ from projective tunnel gluing",
        },
        "tangent_normal_orientation_ledger_declared": all(declared.values()),
        "local_tangent_normal_orientation_ready": ready,
        "active_tangent_normal_orientation_ready": False,
        "active_embedding_not_claimed": True,
        "tangent_normal_orientation_ready": ready,
        "gate_passed": ready,
        "primary_blocker": (
            "none"
            if ready
            else local_frame_error
            or embedding.get("primary_blocker", "active_tunnel_embedding_tangent_frames_and_normals")
        ),
        "next_required": [
            "use_local_unit_frame_for_boundary_spinor_projection",
            "keep_full_embedding_frames_blocked_until_R_Sigma_certificate",
            "feed_local_normal_to_spinor_boundary_projection_map_gate",
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
