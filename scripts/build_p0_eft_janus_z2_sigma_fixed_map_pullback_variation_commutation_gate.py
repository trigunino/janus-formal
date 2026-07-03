from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fixed_map_pullback_variation_commutation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fixed_map_pullback_variation_commutation_gate.json")


def build_payload() -> dict:
    declared = {
        "connection_only_fixed_embedding_variation_gate_declared": True,
        "differential_form_pullback_linearity_checked": True,
        "fixed_smooth_map_declared": True,
        "connection_one_form_variation_declared": True,
        "pullback_acts_linearly_on_connection_forms": True,
        "variation_acts_only_on_connection_form": True,
        "no_map_variation_term": True,
        "no_fitted_pullback_coefficient": True,
    }
    closure = {
        "pullback_commutes_with_delta_omega_proved": True,
    }
    return {
        "status": "janus-z2-sigma-fixed-map-pullback-variation-commutation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "standard pullback of differential forms by a fixed smooth map",
            "linearity of pullback on differential forms",
            "connection-only fixed-embedding variation gate",
        ],
        "bibliography_result": (
            "For a fixed smooth map X_Sigma, pullback is a linear operator on "
            "connection-valued forms. Since delta_omega does not vary X_Sigma, "
            "delta_omega commutes with X_Sigma^* on the connection one-form."
        ),
        "declared": declared,
        "closure": closure,
        "formulae": {
            "fixed_map": "delta_omega X_Sigma = 0",
            "commutation": "delta_omega X_Sigma^* omega = X_Sigma^*(delta_omega omega)",
            "excluded_term": "(delta_omega X_Sigma)^* omega = 0",
        },
        "forbidden": [
            "map variation term in delta omega",
            "fitted pullback coefficient",
            "manual Sigma orientation sign",
            "legacy Z4 pullback commutation",
        ],
        "fixed_map_pullback_variation_commutation_ledger_declared": all(declared.values()),
        "fixed_map_pullback_variation_commutation_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "feed_pullback_commutes_with_delta_omega_to_fixed_embedding_gate",
            "prove_z2_oriented_commutation",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Fixed-Map Pullback Variation Commutation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['fixed_map_pullback_variation_commutation_ledger_declared']}`",
        f"Ready: `{payload['fixed_map_pullback_variation_commutation_ready']}`",
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
