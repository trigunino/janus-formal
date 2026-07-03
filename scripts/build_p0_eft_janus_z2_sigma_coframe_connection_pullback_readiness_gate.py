from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate.json")


def build_payload() -> dict:
    declared = {
        "active_embedding_from_radius_gate_imported": True,
        "embedding_tangent_frame_transport_gate_imported": True,
        "tangent_normal_orientation_gate_imported": True,
        "coframe_connection_pullback_gate_imported": True,
        "pullback_coframe_connection_bibliography_checked": True,
    }
    readiness = {
        "active_embedding_ready": False,
        "tangent_frame_ready": False,
        "normal_orientation_ready": False,
        "differential_form_pullback_ready": True,
        "coframe_pullback_formula_ready": True,
        "spin_connection_pullback_formula_ready": True,
        "coframe_pullback_ready": False,
        "spin_connection_pullback_ready": False,
        "coframe_connection_pullback_ready": False,
    }
    return {
        "status": "janus-z2-sigma-coframe-connection-pullback-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "standard differential-form pullback functoriality",
            "Cartan/tetrad coframe formalism",
            "spin-connection one-form formalism",
            "thin-shell embedding tangent-frame construction",
        ],
        "source_links": [
            "https://ncatlab.org/nlab/show/differential%2Bform",
            "https://ncatlab.org/nlab/show/Cartan%2Bstructural%2Bequations",
            "https://link.aps.org/doi/10.1103/PhysRevD.105.064066",
        ],
        "bibliography_result": (
            "The literature supplies the functorial pullback of coframe and spin-connection "
            "forms once the active embedding is known. It does not supply the Janus "
            "resolved-tunnel embedding X_+/- or its tangent/normal frame."
        ),
        "declared": declared,
        "readiness": readiness,
        "formulae": {
            "coframe_pullback": "e^I_Sigma = X_Sigma^*(e^I)",
            "spin_connection_pullback": "omega^I_J|_Sigma = X_Sigma^*(omega^I_J)",
            "tangent_frame_dependency": "E_a^mu = partial_a X^mu",
            "normal_dependency": "h_ab and n_mu are induced by X_Sigma and orientation",
        },
        "closed": [
            "differential_form_pullback_ready",
            "coframe_pullback_formula_ready",
            "spin_connection_pullback_formula_ready",
        ],
        "still_open": [
            "active_embedding_ready",
            "tangent_frame_ready",
            "normal_orientation_ready",
            "coframe_pullback_ready",
            "spin_connection_pullback_ready",
            "coframe_connection_pullback_ready",
        ],
        "coframe_connection_pullback_readiness_ledger_declared": all(declared.values()),
        "coframe_connection_pullback_readiness_ready": all(declared.values()) and all(readiness.values()),
        "next_required": [
            "close_active_tunnel_embedding_from_radius_gate",
            "derive_tangent_frames_from_X_plus_minus_of_a",
            "derive_unit_normals_from_active_embedding_and_Z2_orientation",
            "evaluate_XSigma_pullback_of_coframe_and_spin_connection",
            "feed_coframe_connection_pullback_to_torsion_pullback_readiness_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Coframe Connection Pullback Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['coframe_connection_pullback_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['coframe_connection_pullback_readiness_ready']}`",
        "",
        "## Closed",
    ]
    lines.extend(f"- `{item}`" for item in payload["closed"])
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
