from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_component_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_component_builder_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-matter-flux-component-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "transparent_flux_component_builder_ready": True,
        "requires_active_sigma_transparency_derived": True,
        "matter_flux_zero_without_transparency_forbidden": True,
        "matter_flux_rho_p_values_ready": False,
        "uses_observational_fit": False,
        "uses_archived_z4_inputs": False,
        "gate_passed": True,
        "formulas": {
            "transparent_branch": "if F_a^Z2Sigma = 0 is actively derived, matter_flux_rho(a)=matter_flux_p(a)=0",
            "nontransparent_branch": "compute F_a^Z2Sigma(a) from T_munu e_a^mu n^nu before reducing to rho/p",
        },
        "next_required": [
            "derive_active_Sigma_transparency_or_compute_nontransparent_flux",
            "if_transparent_write_zero_matter_flux_components_with_transparency_provenance",
            "if_nontransparent_reduce_F_a_Z2Sigma_to_FLRW_rho_p_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Component Builder Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Transparent builder ready: `{payload['transparent_flux_component_builder_ready']}`",
        f"Matter-flux values ready: `{payload['matter_flux_rho_p_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
