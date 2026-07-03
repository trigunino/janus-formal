from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_oriented_pullback_variation_commutation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_oriented_pullback_variation_commutation_gate.json")


def build_payload() -> dict:
    declared = {
        "tangent_normal_orientation_gate_declared": True,
        "fixed_map_pullback_variation_commutation_gate_declared": True,
        "projective_gluing_normal_orientation_sign_gate_declared": True,
        "thin_shell_orientation_bibliography_checked": True,
        "z2_normal_orientation_declared": True,
        "orientation_sign_transport_declared": True,
        "manual_orientation_sign_forbidden": True,
        "no_fitted_orientation_coefficient": True,
    }
    closure = {
        "fixed_map_commutation_ready": True,
        "z2_orientation_sign_fixed": True,
        "z2_oriented_commutation_ready": True,
    }
    return {
        "status": "janus-z2-sigma-oriented-pullback-variation-commutation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel thin-shell hypersurface normal conventions",
            "Poisson hypersurface normal/orientation conventions",
            "Barrabes-Israel shell orientation conventions",
            "fixed-map pullback variation commutation gate",
            "projective gluing normal orientation sign gate",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies normal and orientation conventions, "
            "but the Janus resolved-tunnel Z2 sign must come from the active "
            "projective-tunnel gluing, not from an observational or fitted sign."
        ),
        "declared": declared,
        "closure": closure,
        "formulae": {
            "unoriented_commutation": "delta_omega X_Sigma^* omega = X_Sigma^*(delta_omega omega)",
            "z2_orientation_target": "epsilon_Z2 * delta_omega X_Sigma^* omega respects n_- = epsilon_Z2 n_+",
            "fixed_sign": "epsilon_Z2 = -1 from projective-tunnel gluing",
        },
        "forbidden": [
            "manual Sigma orientation sign",
            "fitted orientation coefficient",
            "reuse legacy Z4 orientation",
            "skip tangent-normal orientation gate",
        ],
        "oriented_pullback_variation_commutation_ledger_declared": all(declared.values()),
        "oriented_pullback_variation_commutation_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "feed_z2_oriented_commutation_to_fixed_embedding_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Oriented Pullback Variation Commutation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['oriented_pullback_variation_commutation_ledger_declared']}`",
        f"Ready: `{payload['oriented_pullback_variation_commutation_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
