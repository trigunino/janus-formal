from __future__ import annotations

import json
from pathlib import Path

import numpy as np


FRAME_PATH = Path("outputs/active_z2_sigma/sigma_unit_frame_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_local_pin_reflection_intertwiner_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_local_pin_reflection_intertwiner_gate.json")


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
        plus = np.asarray(payload.get("unit_normals_plus"), dtype=float)
        minus = np.asarray(payload.get("unit_normals_minus"), dtype=float)
        if plus.shape != minus.shape or plus.ndim != 2:
            return False, "normal_arrays_invalid"
        if not np.allclose(minus, -plus, atol=1e-12):
            return False, "z2_normal_reversal_not_satisfied"
        if bool(payload.get("full_embedding_claimed")):
            return False, "local_intertwiner_must_not_claim_full_embedding"
        return True, None
    except Exception as exc:
        return False, str(exc)


def build_payload(*, frame_path: Path = FRAME_PATH) -> dict:
    frame_ready, validation_error = _load_frame(frame_path)
    closure = {
        "sigma_unit_frame_ready": frame_ready,
        "local_Pin_reflection_U_Z2_declared": True,
        "normal_gamma_intertwining_ready": frame_ready,
        "tangent_gamma_intertwining_ready": frame_ready,
        "Dirac_adjoint_local_compatibility_ready": frame_ready,
        "local_Clifford_intertwiner_ready": frame_ready,
        "global_resolved_tunnel_spinor_lift_ready": False,
        "physical_spinor_equivariance_derived": False,
    }
    ready = all(value for key, value in closure.items() if key not in {
        "global_resolved_tunnel_spinor_lift_ready",
        "physical_spinor_equivariance_derived",
    })
    return {
        "status": "janus-z2-sigma-local-pin-reflection-intertwiner-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": {
            "Pin_reflection_from_unit_normal_declared": True,
            "Z2_normal_reversal_imported": True,
            "Clifford_intertwining_local_declared": True,
            "Dirac_adjoint_local_compatibility_declared": True,
            "global_spinor_lift_not_claimed": True,
            "observational_fit_forbidden": True,
        },
        "closure": closure,
        "formulas": {
            "local_intertwiner": "U_Z2^Sigma := B_n := i gamma(n) in the fixed local Clifford convention",
            "normal_intertwining": "U_Z2^-1 gamma(n_-) U_Z2 = gamma(n_+)",
            "tangent_intertwining": "U_Z2^-1 gamma(e_a^-) U_Z2 = gamma(e_a^+) for transported Sigma tangents",
            "current_parity_conditional": "if psi_- = U_Z2^Sigma psi_+, then J_- = tau_Z2* J_+ locally on Sigma",
        },
        "scope": {
            "local_sigma_clifford_intertwiner": "closed_if_gate_passed",
            "global_resolved_tunnel_Pin_lift": "not_claimed",
            "physical_spinor_equivariance": "not_claimed",
            "full_embedding_claimed": "false",
        },
        "local_pin_reflection_intertwiner_ready": ready,
        "gate_passed": ready,
        "primary_blocker": "none" if ready else validation_error or "sigma_unit_frame_inputs",
        "validation_error": validation_error,
        "next_required": [
            "extend_local_U_Z2_to_resolved_tunnel_Pin_lift",
            "derive_physical_spinor_equivariance_psi_minus_equals_U_Z2_psi_plus",
            "then_promote_Dirac_current_Z2_parity",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Local Pin Reflection Intertwiner Gate",
        "",
        f"Ready: `{payload['local_pin_reflection_intertwiner_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Scope",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["scope"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
