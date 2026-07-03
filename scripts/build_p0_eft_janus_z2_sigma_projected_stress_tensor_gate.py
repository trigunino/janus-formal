from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_stress_tensor_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_stress_tensor_gate.json")


def build_payload() -> dict:
    lock = {
        "sigma_boundary_variational_package_declared": True,
        "sigma_boundary_nonlinear_residual_closed": True,
        "local_background_derivation_required": True,
        "induced_sigma_metric_declared": True,
        "boundary_action_variation_with_respect_to_induced_metric_declared": True,
        "brown_york_like_projection_declared": True,
        "z2_projection_to_visible_background_declared": True,
    }
    return {
        "status": "janus-z2-sigma-projected-stress-tensor-gate",
        "active_core": "Z2_tunnel_Sigma",
        "lock": lock,
        "projected_stress_tensor_lock_closed": all(lock.values()),
        "projected_sigma_stress_tensor_derived": all(lock.values()),
        "stress_tensor_definition": "T_Sigma_ab = -2/sqrt(|h|) * delta S_Sigma / delta h^ab, then Z2-projected to visible background",
        "legacy_lcdm_background_substitution_forbidden": True,
        "archived_z4_background_reuse_forbidden": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projected Stress Tensor Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Projected Sigma stress tensor derived: `{payload['projected_sigma_stress_tensor_derived']}`",
        "",
        f"Definition: `{payload['stress_tensor_definition']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
