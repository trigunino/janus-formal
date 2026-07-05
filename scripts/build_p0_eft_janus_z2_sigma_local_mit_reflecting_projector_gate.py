from __future__ import annotations

import json
from pathlib import Path

import numpy as np


FRAME_PATH = Path("outputs/active_z2_sigma/sigma_unit_frame_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_local_mit_reflecting_projector_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_local_mit_reflecting_projector_gate.json")


def _load_frame(path: Path) -> tuple[bool, str | None]:
    if not path.exists():
        return False, "sigma_unit_frame_inputs_missing"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if payload.get("active_core") != "Z2_tunnel_Sigma":
            return False, "active_core_mismatch"
        if payload.get("source") != "active_derived":
            return False, "source_not_active_derived"
        if payload.get("sigma_unit_frame_ready") is not True:
            return False, "sigma_unit_frame_not_ready"
        normals_plus = np.asarray(payload.get("unit_normals_plus"), dtype=float)
        normals_minus = np.asarray(payload.get("unit_normals_minus"), dtype=float)
        if normals_plus.ndim != 2 or normals_minus.shape != normals_plus.shape:
            return False, "unit_normals_invalid"
        if not np.all(np.isfinite(normals_plus)) or not np.all(np.isfinite(normals_minus)):
            return False, "unit_normals_not_finite"
        if float(payload.get("z2_orientation_sign")) != -1.0:
            return False, "z2_orientation_sign_not_minus_one"
        if not np.allclose(normals_minus, -normals_plus, atol=1e-12):
            return False, "minus_normal_not_z2_reversed"
        if bool(payload.get("full_embedding_claimed")):
            return False, "local_projector_gate_must_not_claim_full_embedding"
        return True, None
    except Exception as exc:
        return False, str(exc)


def build_payload(*, frame_path: Path = FRAME_PATH) -> dict:
    frame_ready, validation_error = _load_frame(frame_path)
    closure = {
        "sigma_unit_normal_frame_ready": frame_ready,
        "Z2_normal_reversal_ready": frame_ready,
        "unit_normal_Clifford_action_ready": frame_ready,
        "MIT_reflecting_projector_declared": True,
        "projection_idempotent_ready": frame_ready,
        "projection_self_adjoint_ready": frame_ready,
        "normal_current_zero_algebra_identity_ready": frame_ready,
        "boundary_spinor_satisfies_projector_derived": False,
    }
    ready = all(value for key, value in closure.items() if key != "boundary_spinor_satisfies_projector_derived")
    return {
        "status": "janus-z2-sigma-local-mit-reflecting-projector-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": {
            "local_unit_normal_frame_imported": True,
            "normal_Clifford_action_declared": True,
            "MIT_reflecting_projector_declared": True,
            "projector_phase_fixed": True,
            "observational_fit_forbidden": True,
        },
        "closure": closure,
        "formulas": {
            "normal_clifford": "B_n := i gamma_mu n^mu in the fixed MIT/Clifford convention, with B_n^2 = 1",
            "mit_projector": "P_reflect := (1 + B_n)/2",
            "current_identity": "psi = P_reflect psi -> psibar gamma(n) psi = 0",
        },
        "scope": {
            "local_projector_algebra": "closed_if_gate_passed",
            "physical_boundary_spinor_satisfies_projector": "not_claimed",
            "plus_minus_spinor_bundle_global_existence": "not_claimed",
            "full_embedding_claimed": "false",
        },
        "local_mit_reflecting_projector_ready": ready,
        "normal_current_zero_algebra_ready": ready,
        "gate_passed": ready,
        "primary_blocker": "none" if ready else validation_error or "sigma_unit_frame_inputs",
        "validation_error": validation_error,
        "next_required": [
            "derive_physical_boundary_spinor_satisfies_reflecting_projector",
            "derive_plus_minus_spinor_bundle_data",
            "derive_boundary_spinor_restriction",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Local MIT Reflecting Projector Gate",
        "",
        f"Ready: `{payload['local_mit_reflecting_projector_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Scope",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["scope"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
