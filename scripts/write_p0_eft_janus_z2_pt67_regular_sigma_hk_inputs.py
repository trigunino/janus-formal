from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_pt67_gluing_orientation import pt67_gluing_orientation_payload
from src.janus_lab.z2_pt67_regular_surface import pt67_regular_surface_geometry

JSON_PATH = Path("outputs/active_z2_sigma/pt67_regular_sigma_hk_inputs.json")


def build_payload() -> dict:
    surface = pt67_regular_surface_geometry()
    gluing = pt67_gluing_orientation_payload()
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "The_Janus_Cosmological_Model chapter 6.7 equations 6.7.2-6.7.4",
        "route": "chapter_6_7_regular_PT_transfer_cross_term_surface",
        "provenance": {
            "surface_report": "outputs/reports/p0_eft_janus_z2_pt67_regular_surface_gate.json",
            "gluing_report": "outputs/reports/p0_eft_janus_z2_pt67_gluing_orientation_gate.json",
            "uses_observational_fit": False,
            "uses_free_orientation_sign": False,
        },
        "h_ab_at_sigma": {
            "h_TT": surface["regularity_at_sigma"]["induced_h_TT"],
            "h_thetatheta": surface["regularity_at_sigma"]["induced_h_thetatheta"],
            "h_phiphi": surface["regularity_at_sigma"]["induced_h_phiphi"],
            "nondegenerate": not surface["regularity_at_sigma"]["induced_surface_degenerate"],
        },
        "unit_normal": {
            **surface["unit_normal"],
            "orientation": "PT gluing fixed by dr -> dr; not outward Israel cut-and-paste normals",
        },
        "K_ab_local": surface["extrinsic_curvature_local"],
        "DeltaK_PT_transport": gluing["DeltaK_PT_transport"],
        "regular_sigma_pipeline_inputs_ready": True,
        "cartan_ghy_jump_ready_under_PT_transport": gluing["raccord_to_regular_sigma_pipeline"][
            "Cartan_GHY_jump_ready_under_PT_transport"
        ],
        "not_claimed": [
            "not a standard outward-normal Israel cut-and-paste jump",
            "not an observational fit",
            "not a null-shell Barrabes-Israel stress tensor",
        ],
    }


def write_outputs() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_outputs(), indent=2))
