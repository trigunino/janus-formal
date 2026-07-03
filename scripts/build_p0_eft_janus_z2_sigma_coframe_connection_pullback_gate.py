from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coframe_connection_pullback_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coframe_connection_pullback_gate.json")


def build_payload() -> dict:
    declared = {
        "coframe_connection_bibliography_checked": True,
        "tetrad_coframe_formalism_imported": True,
        "spin_connection_formalism_imported": True,
        "differential_form_pullback_imported": True,
        "active_Sigma_embedding_required": True,
        "tangent_normal_orientation_gate_declared": True,
        "projective_gluing_normal_orientation_sign_gate_declared": True,
        "coframe_pullback_declared": True,
        "spin_connection_pullback_declared": True,
        "Z2_normal_orientation_required": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "active_Sigma_embedding_ready": False,
        "coframe_pullback_ready": False,
        "spin_connection_pullback_ready": False,
        "Z2_oriented_pullback_ready": True,
        "coframe_connection_pullback_ready": False,
    }
    return {
        "status": "janus-z2-sigma-coframe-connection-pullback-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "tetrad/coframe first-order gravity literature",
            "spin-connection and Cartan-structure-equation references",
            "standard differential-form pullback references",
            "active tangent-normal/Z2 orientation gate",
            "projective gluing normal orientation sign gate",
        ],
        "bibliography_result": (
            "Generic first-order geometry supplies coframe e^I, spin connection "
            "omega^I_J and pullback X_Sigma^*. It does not supply the active Janus "
            "resolved-tunnel embedding or its Z2 normal orientation."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "coframe_pullback": "e^I_Sigma = X_Sigma^*(e^I)",
            "connection_pullback": "omega^I_J|_Sigma = X_Sigma^*(omega^I_J)",
            "oriented_pullback": "epsilon_Z2=-1 fixes the normal sign used by X_+ and X_-",
        },
        "coframe_connection_pullback_ledger_declared": all(declared.values()),
        "coframe_connection_pullback_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_active_tunnel_embedding_of_a_gate",
            "pass_tangent_normal_orientation_gate",
            "derive_X_Sigma_plus_minus_of_a",
            "derive_tangent_and_normal_frames_on_Sigma",
            "pull_back_coframe_to_Sigma",
            "pull_back_spin_connection_to_Sigma",
            "feed_coframe_connection_pullback_to_torsion_pullback_on_Sigma_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coframe Connection Pullback Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['coframe_connection_pullback_ledger_declared']}`",
        f"Pullback ready: `{payload['coframe_connection_pullback_ready']}`",
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
