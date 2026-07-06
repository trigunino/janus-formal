from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_intrinsic_curvature_policy_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_intrinsic_curvature_policy_gate.json"
)


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-surface-intrinsic-curvature-policy-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "bibliography_informed_policy_audit",
        "bibliography_checked": [
            "DGP/induced-gravity brane actions: brane-localized Einstein-Hilbert terms are legitimate explicit action terms",
            "brane-world curvature corrections: intrinsic curvature corrections can regularize or modify brane cosmology",
            "D-brane curvature corrections: curvature terms can arise from higher-derivative/string corrections",
        ],
        "policy": {
            "surface_intrinsic_curvature_term_C_Rh_legitimate": True,
            "surface_intrinsic_curvature_term_already_in_active_Janus_action": False,
            "topology_Z2_forces_C": False,
            "C_can_be_introduced_as_new_explicit_extension": True,
            "C_can_be_used_as_hidden_fit_parameter": False,
        },
        "impact_on_RSigma": {
            "needed_for_finite_radius_with_B": True,
            "finite_radius_formula_if_adopted": "R_Sigma^2 = -2 C / B",
            "requires_opposite_signs": True,
            "requires_C_over_B_from_action_or_quantization": True,
        },
        "gate_passed": True,
        "primary_blocker": "decide_or_derive_surface_intrinsic_curvature_extension_C",
        "next_required": [
            "either derive C from Janus tunnel core microphysics",
            "or explicitly adopt C R[h] as a new extension with anti-rustine status",
            "or reject C and keep R_Sigma as open modulus",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface Intrinsic Curvature Policy Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Policy",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["policy"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
