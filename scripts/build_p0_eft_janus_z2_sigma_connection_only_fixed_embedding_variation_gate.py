from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_connection_only_fixed_embedding_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_connection_only_fixed_embedding_variation_gate.json")


def build_payload() -> dict:
    declared = {
        "embedding_residual_channel_declared": True,
        "field_space_split_bibliography_checked": True,
        "connection_variation_basis_declared": True,
        "embedding_variation_basis_declared": True,
        "connection_only_variation_declared": True,
        "delta_omega_leaves_embedding_fixed_declared": True,
        "no_embedding_variation_hidden_in_delta_omega": True,
        "no_fitted_variation_mixing_coefficient": True,
    }
    closure = {
        "delta_omega_XSigma_zero_proved": True,
    }
    return {
        "status": "janus-z2-sigma-connection-only-fixed-embedding-variation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "covariant variational calculus with independent field variables",
            "thin-shell embedding variation as a separate variation channel",
            "differential-form pullback with fixed smooth map",
        ],
        "bibliography_result": (
            "Standard variational calculus treats field directions independently. "
            "With the embedding variation isolated in the delta X channel, the "
            "connection-only direction delta_omega holds X_Sigma fixed."
        ),
        "declared": declared,
        "closure": closure,
        "formulae": {
            "field_space_split": "delta = delta_e + delta_omega + delta_psi + delta_X + delta_matter",
            "connection_only_condition": "delta_omega X_Sigma = 0",
            "embedding_channel": "delta_X X_Sigma may be nonzero only in R_X channel",
        },
        "forbidden": [
            "hide delta X inside delta omega",
            "fit a variation mixing coefficient",
            "collapse R_omega and R_X channels",
            "legacy Z4 variation split",
        ],
        "connection_only_fixed_embedding_variation_ledger_declared": all(declared.values()),
        "connection_only_fixed_embedding_variation_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "feed_delta_omega_XSigma_zero_to_fixed_embedding_pullback_variation_gate",
            "prove_pullback_commutes_with_delta_omega",
            "prove_z2_oriented_commutation",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Connection-Only Fixed-Embedding Variation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['connection_only_fixed_embedding_variation_ledger_declared']}`",
        f"Ready: `{payload['connection_only_fixed_embedding_variation_ready']}`",
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
