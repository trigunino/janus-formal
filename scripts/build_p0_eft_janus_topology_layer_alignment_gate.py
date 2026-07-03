from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_topology_layer_alignment_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_topology_layer_alignment_gate.json")


def build_payload() -> dict:
    projective = {
        "global_topology": "S4_to_RP4_antipodal_quotient",
        "cover_group": "Z2",
        "sphere_four_cover_defined": True,
        "antipodal_involution_defined": True,
        "antipodal_action_free": True,
        "projective_quotient_defined": True,
        "two_fold_cover_derived": True,
        "big_bang_pole_defined": True,
        "big_crunch_pole_defined": True,
        "antipodal_poles_coincide": True,
        "antipodal_quotient_singular_orbifold": False,
        "cyclic_z4_derived_from_cover": False,
    }
    tunnel = {
        "initial_singularities_present": True,
        "big_bang_big_crunch_coincidence": True,
        "tubular_replacement_defined": True,
        "tunnel_connects_two_folds": True,
        "singularities_removed_by_tunnel": True,
        "tunnel_layer_separate_from_free_quotient": True,
        "orbifold_word_policy": "use only for quotient_plus_tunnel_membrane_layer, not pure free antipodal quotient",
    }
    boy = {
        "sphere_two_shadow_defined": True,
        "projective_plane_shadow_defined": True,
        "boy_immersion_didactic_only": True,
        "not_global_four_dimensional_topology": True,
    }
    sectors = {
        "sheet_symmetry": "Z2",
        "charge_symmetry": "Z2",
        "natural_four_sector_group": "Z2xZ2",
        "cyclic_z4_monodromy_proved": False,
        "z4_label_policy": "four_sector_packaging_until_order4_monodromy_proved",
        "cyclic_z4_inference_allowed": False,
    }
    aps = {
        "rp4_orientable": False,
        "rp2_boy_shadow_pin_minus_plausible": True,
        "rp4_pin_sign_recheck_required": True,
        "pin_minus_not_promoted_from_boy_shadow_to_rp4": True,
    }
    return {
        "status": "janus-topology-layer-alignment-gate",
        "projective_topology": projective,
        "tunnel_surgery": tunnel,
        "boy_surface_shadow": boy,
        "four_sector_symmetry": sectors,
        "aps_pin_impact": aps,
        "topological_z2_cover_does_not_imply_cyclic_z4": True,
        "no_fit_promotion_allowed_from_z4_packaging": False,
        "next_required": [
            "prove_order4_monodromy_before_cyclic_Z4_claim",
            "recompute_Pin_sign_for_RP4_APS_boundary_before_closing_APS_Pin",
            "keep_orbifold_2_to_1_as_projective_tunnel_cover_ratio_not_cyclic_Z4",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Topology Layer Alignment Gate",
        "",
        f"Global topology: `{payload['projective_topology']['global_topology']}`",
        f"Cover group: `{payload['projective_topology']['cover_group']}`",
        f"Antipodal poles coincide: `{payload['projective_topology']['antipodal_poles_coincide']}`",
        f"Tunnel connects two folds: `{payload['tunnel_surgery']['tunnel_connects_two_folds']}`",
        f"Cyclic Z4 from cover: `{payload['projective_topology']['cyclic_z4_derived_from_cover']}`",
        f"Natural four-sector group: `{payload['four_sector_symmetry']['natural_four_sector_group']}`",
        f"Z4 label policy: `{payload['four_sector_symmetry']['z4_label_policy']}`",
        f"RP4 Pin sign recheck required: `{payload['aps_pin_impact']['rp4_pin_sign_recheck_required']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
