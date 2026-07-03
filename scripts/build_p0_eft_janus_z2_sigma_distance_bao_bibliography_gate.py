from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_distance_bao_bibliography_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_distance_bao_bibliography_gate.json")


def build_payload() -> dict:
    sources = {
        "janus_2024_photon_two_fold_context": {
            "url": "https://arxiv.org/abs/2412.04644",
            "supports": [
                "two_fold_bimetric_context",
                "photons_as_neutral_particles_across_folds",
                "FLRW_type_metrics_for_two_mass_sectors",
            ],
        },
        "hogg_distance_measures": {
            "url": "https://ned.ipac.caltech.edu/level5/Hogg/paper.pdf",
            "supports": [
                "radial_null_trajectory_distance_measures",
                "D_M_D_A_D_L_standard_definitions",
            ],
        },
        "etherington_distance_duality": {
            "url": "https://arxiv.org/abs/2112.05701",
            "supports": [
                "metric_theory_null_geodesic_distance_duality",
                "photon_number_conservation_guard",
            ],
        },
        "bao_sound_horizon": {
            "url": "https://ui.adsabs.harvard.edu/abs/2021PhRvD.104d3521A/abstract",
            "supports": [
                "drag_epoch_sound_horizon_context",
                "Eisenstein_Hu_style_r_d_calibration_context",
            ],
        },
    }
    return {
        "status": "janus-z2-sigma-distance-bao-bibliography-gate",
        "active_core": "Z2_tunnel_Sigma",
        "sources": sources,
        "janus_photon_geodesic_source_found": True,
        "standard_flrw_distance_source_found": True,
        "etherington_reciprocity_source_found": True,
        "bao_sound_horizon_source_found": True,
        "complete_sigma_photon_distance_map_found": False,
        "complete_z2_sigma_sound_ruler_found": False,
        "local_distance_and_ruler_derivation_required": True,
        "may_import_standard_null_distance_definitions": True,
        "may_import_etherington_guard_conditionally": True,
        "must_derive_sigma_photon_geodesic_map_locally": True,
        "must_derive_z2_sigma_rd_locally": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Distance/BAO Bibliography Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Complete Sigma photon distance map found: `{payload['complete_sigma_photon_distance_map_found']}`",
        f"Complete Z2/Sigma sound ruler found: `{payload['complete_z2_sigma_sound_ruler_found']}`",
        f"Local derivation required: `{payload['local_distance_and_ruler_derivation_required']}`",
        "",
        "## Sources",
    ]
    for name, row in payload["sources"].items():
        lines.append(f"- `{name}`: {row['url']}")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
