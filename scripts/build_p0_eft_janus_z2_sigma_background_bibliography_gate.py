from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_bibliography_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_bibliography_gate.json")


def build_payload() -> dict:
    sources = {
        "janus_2024_projective_tunnel": {
            "url": "https://arxiv.org/abs/2412.04644",
            "supports": [
                "S4_to_RP4_projective_cover",
                "tubular_replacement_of_big_bang_big_crunch",
                "bimetric_FLRW_solution",
                "generalized_two_sector_energy_conservation",
            ],
        },
        "junction_boundary_formalism": {
            "url": "https://arxiv.org/abs/2412.21167",
            "supports": [
                "GHY_boundary_method",
                "junction_conditions_from_boundary_terms",
            ],
        },
        "einstein_cartan_holst_cosmology": {
            "url": "https://arxiv.org/html/2406.14982v2",
            "supports": [
                "modified_Holst_term",
                "fermion_spin_connection_coupling",
                "effective_pseudoscalar_torsion_sector",
            ],
        },
    }
    return {
        "status": "janus-z2-sigma-background-bibliography-gate",
        "active_core": "Z2_tunnel_Sigma",
        "sources": sources,
        "janus_projective_tunnel_topology_source_found": True,
        "janus_bimetric_flrw_source_found": True,
        "junction_boundary_formalism_source_found": True,
        "einstein_cartan_holst_cosmology_source_found": True,
        "complete_z2_sigma_background_equations_found": False,
        "local_derivation_required": True,
        "may_import_generic_junction_formalism": True,
        "may_import_generic_holst_torsion_blocks": True,
        "must_derive_projected_sigma_background_locally": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Background Bibliography Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Complete Z2/Sigma background equations found: `{payload['complete_z2_sigma_background_equations_found']}`",
        f"Local derivation required: `{payload['local_derivation_required']}`",
        "",
        "## Sources",
    ]
    for name, row in payload["sources"].items():
        lines.append(f"- `{name}`: {row['url']}")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
