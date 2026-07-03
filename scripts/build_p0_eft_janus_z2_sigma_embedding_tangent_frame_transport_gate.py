from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_embedding_tangent_frame_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_embedding_tangent_frame_transport_gate.json")


def build_payload() -> dict:
    declared = {
        "active_embedding_from_radius_gate_declared": True,
        "embedded_submanifold_tangent_bibliography_checked": True,
        "thin_shell_tangent_frame_bibliography_checked": True,
        "X_plus_minus_of_a_input_declared": True,
        "coordinate_derivative_formula_declared": True,
        "tangent_frame_transport_map_declared": True,
        "no_fitted_tangent_frame": True,
    }
    closure = {
        "X_plus_minus_of_a_ready": False,
        "tangent_frames_from_embedding_ready": False,
    }
    return {
        "status": "janus-z2-sigma-embedding-tangent-frame-transport-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "embedded submanifold tangent map references",
            "thin-shell tangent basis e_a^mu = partial_a X^mu references",
            "active tunnel embedding from radius gate",
        ],
        "bibliography_result": (
            "Standard differential geometry and thin-shell literature derive tangent "
            "frames from the differential of the embedding. The active Janus input "
            "still requires X_+/- (a), not a fitted frame."
        ),
        "declared": declared,
        "closure": closure,
        "formulae": {
            "embedding": "X_pm^mu(y^a): Sigma -> M_pm",
            "tangent_frame": "E_a_pm^mu = partial X_pm^mu / partial y^a",
            "transport": "X_+/- (a) -> dX_+/- (a) -> E_a^mu(a)",
        },
        "forbidden": [
            "fitted tangent frame",
            "manual frame rotation",
            "bypass X_plus_minus_of_a",
            "legacy Z4 tangent frame import",
        ],
        "embedding_tangent_frame_transport_ledger_declared": all(declared.values()),
        "embedding_tangent_frame_transport_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "derive_X_plus_minus_of_a",
            "feed_tangent_frames_to_tangent_normal_orientation_gate",
            "feed_tangent_frames_to_coframe_connection_pullback_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Embedding Tangent Frame Transport Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['embedding_tangent_frame_transport_ledger_declared']}`",
        f"Ready: `{payload['embedding_tangent_frame_transport_ready']}`",
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
