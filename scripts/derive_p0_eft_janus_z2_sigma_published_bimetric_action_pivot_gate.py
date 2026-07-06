from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_published_bimetric_action_pivot_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_published_bimetric_action_pivot_gate.json"
)


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-published-bimetric-action-pivot-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source_pdf": "The_Janus_Cosmological_Model.pdf",
        "published_reference_pages": {
            "pedagogical_action_variation": "73-81",
            "epjc_compact_action": "223-226",
            "bianchi_status": "226-232",
            "wormhole_throat": "177-189",
            "projective_topology": "190-195",
        },
        "previous_starting_point": "local_Sigma_counterterm_first",
        "previous_starting_point_underselected": True,
        "new_starting_point": "published_bulk_bimetric_action_plus_bianchi_first",
        "model_changed": False,
        "route_changed": True,
        "active_topology_kept": True,
        "z2_tunnel_sigma_kept": True,
        "z4_not_reopened": True,
        "sigma_surface_action_extension_allowed": False,
        "published_action_supplies": [
            "two metrics on one manifold",
            "determinant bridge factors",
            "interaction tensors as action-derived source slots",
            "Bianchi constraints on source slots",
            "Newtonian/TOV checked sectors",
        ],
        "published_action_does_not_supply": [
            "complete nonlinear interaction tensor",
            "local Sigma counterterm density L_Sigma(h,K)",
            "surface-HK coefficients a0..a3",
            "sigma_alpha_h",
        ],
        "next_derivation_order": [
            "derive symmetry-reduced interaction tensor slots from published bimetric action",
            "enforce Bianchi in the reduced sector before any Sigma counterterm",
            "transport the reduced source to Sigma only after Bianchi closure",
            "then revisit whether a separate Sigma counterterm is still needed",
        ],
        "forbidden_shortcuts": [
            "invent L_Sigma before bulk Bianchi source reduction",
            "set interaction tensor freely without Bianchi",
            "claim full nonlinear closure from Newtonian/TOV checks",
            "reuse archived Z4",
        ],
        "pivot_passed": True,
        "full_no_fit_prediction_ready": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Published Bimetric Action Pivot Gate",
        "",
        f"Previous starting point: `{payload['previous_starting_point']}`",
        f"Previous underselected: `{payload['previous_starting_point_underselected']}`",
        f"New starting point: `{payload['new_starting_point']}`",
        f"Model changed: `{payload['model_changed']}`",
        f"Route changed: `{payload['route_changed']}`",
        f"Pivot passed: `{payload['pivot_passed']}`",
        "",
        "## Next Derivation Order",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_derivation_order"])
    lines.extend(["", "## Forbidden Shortcuts"])
    lines.extend(f"- `{item}`" for item in payload["forbidden_shortcuts"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
