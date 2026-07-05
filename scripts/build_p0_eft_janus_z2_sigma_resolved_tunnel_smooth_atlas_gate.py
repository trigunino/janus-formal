from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_collar_tubular_neighborhood_gate import (
    build_payload as build_collar_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_resolved_tunnel_smooth_atlas_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_resolved_tunnel_smooth_atlas_gate.json")


def build_payload() -> dict:
    collar = build_collar_payload()
    declared = {
        "tubular_neighborhood_bibliography_checked": True,
        "collar_gluing_bibliography_checked": True,
        "projective_tunnel_interface_declared": True,
        "collar_tubular_neighborhood_gate_declared": True,
        "frame_bundle_gate_declared": True,
        "polar_neighborhood_removal_declared": True,
        "tubular_throat_chart_declared": True,
        "smooth_gluing_map_declared": True,
        "resolved_atlas_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "projective_tunnel_topology_ready": True,
        "collars_derived": collar["collar_tubular_neighborhood_ready"],
        "tubular_replacement_smooth_derived": False,
        "gluing_map_smooth_derived": False,
        "transition_maps_smooth_derived": False,
        "resolved_tunnel_atlas_derived": False,
        "smooth_atlas_ready": False,
    }
    return {
        "status": "janus-z2-sigma-resolved-tunnel-smooth-atlas-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "tubular neighborhood theorem",
            "collar neighborhood theorem",
            "smooth gluing along collars",
            "active collar/tubular neighborhood gate",
            "active projective tunnel interface",
        ],
        "source_links": [
            "https://ncatlab.org/nlab/show/tubular+neighbourhood",
            "https://ncatlab.org/nlab/show/collar+neighbourhood+theorem",
            "https://msp.org/agt/2007/7-1/agt-v7-n1-p01-p.pdf",
            "https://jfdavis.pages.iu.edu/teaching/m623/smooth_structures_and_handles.pdf",
        ],
        "bibliography_result": (
            "Standard differential topology gives smooth tubular/collar charts and "
            "smooth gluing criteria. The Janus-specific proof still has to derive "
            "the collars, throat chart, gluing map, and transition maps for the "
            "resolved projective tunnel."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "collar_tubular_neighborhood": {
                "gate": collar["status"],
                "ready": collar["collar_tubular_neighborhood_ready"],
                "closure": collar["closure"],
                "primary_blocker": collar.get("primary_blocker"),
            },
        },
        "formulas": {
            "collar": "partial M x [0, eps) -> M",
            "tube_chart": "Sigma x (-eps, eps) -> U_Sigma",
            "gluing": "phi_pm = collar_minus^{-1} o collar_plus",
            "atlas": "A_res = A_plus union A_minus union A_tube with smooth transitions",
        },
        "resolved_tunnel_smooth_atlas_ledger_declared": all(declared.values()),
        "resolved_tunnel_smooth_atlas_ready": all(declared.values()) and all(closure.values()),
        "standard_smooth_gluing_theorems_available": True,
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else collar.get("primary_blocker", "collar_tubular_neighborhood")
        ),
        "next_required": [
            "pass_collar_tubular_neighborhood_gate",
            "derive_collar_neighborhoods",
            "prove_tubular_replacement_is_smooth",
            "derive_smooth_gluing_map",
            "prove_transition_maps_smooth",
            "feed_result_to_resolved_tunnel_frame_bundle_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Resolved Tunnel Smooth Atlas Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['resolved_tunnel_smooth_atlas_ledger_declared']}`",
        f"Smooth atlas ready: `{payload['resolved_tunnel_smooth_atlas_ready']}`",
        "",
        "## Bibliography",
        payload["bibliography_result"],
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
