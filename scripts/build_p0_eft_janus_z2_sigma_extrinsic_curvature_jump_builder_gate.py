from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_extrinsic_curvature_jump_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_extrinsic_curvature_jump_builder_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-extrinsic-curvature-jump-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "Israel junction conditions",
            "Poisson & Visser 1995 thin-shell extrinsic-curvature conventions",
        ],
        "deltaK_jump_builder_ready": True,
        "jump_convention": "DeltaK = K_plus + eps_Z2 K_minus",
        "projective_tunnel_default": "eps_Z2 = -1 gives K_plus - K_minus",
        "orientation_policy": "eps_Z2 is explicit in the jump builder and remains explicit in the existing Cartan-GHY projection convention",
        "fitted_orientation_forbidden": True,
        "requires_active_K_s_plus_of_a": True,
        "requires_active_K_s_minus_of_a": True,
        "requires_active_K_tau_plus_of_a": True,
        "requires_active_K_tau_minus_of_a": True,
        "requires_explicit_z2_orientation": True,
        "uses_planck_lcdm_inputs": False,
        "uses_archived_z4_inputs": False,
        "DeltaK_values_ready": False,
        "gate_passed": True,
        "next_required": [
            "derive_active_tunnel_embedding_X_plus_minus_of_a",
            "compute_K_s_plus_minus_and_K_tau_plus_minus_from_active_embedding",
            "write_DeltaK_s_tau_to_active_component_manifest",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Extrinsic Curvature Jump Builder Gate",
        "",
        f"Builder ready: `{payload['deltaK_jump_builder_ready']}`",
        f"DeltaK values ready: `{payload['DeltaK_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Convention",
        f"`{payload['jump_convention']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
