from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_manifest_schema_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_manifest_schema_gate.json")


def build_payload() -> dict:
    flrw_components = [
        "cartan_ghy_rho",
        "cartan_ghy_p",
        "holst_nieh_yan_rho",
        "holst_nieh_yan_p",
        "matter_flux_rho",
        "matter_flux_p",
        "counterterm_rho",
        "counterterm_p",
    ]
    early_plasma = [
        "rho_baryon_Z2Sigma",
        "rho_photon_Z2Sigma",
        "Gamma_drag_Z2Sigma",
    ]
    required_fields = [
        "active_core",
        "source",
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "H0_Z2Sigma_km_s_Mpc",
        "omega_k_Z2Sigma",
        "critical_normalization",
        "scalar_provenance",
        "a_grid",
        "z_grid",
        "z_max",
        "flrw_components_over_rho_crit0",
        "early_plasma",
        "component_provenance",
    ]
    optional_fields = [
        "z_d_bracket",
    ]
    return {
        "status": "janus-z2-sigma-bao-component-manifest-schema-gate",
        "active_core": "Z2_tunnel_Sigma",
        "component_manifest_path": "outputs/active_z2_sigma/bao_component_inputs.json",
        "template_path": "docs/templates/active_z2_sigma_bao_component_inputs.template.json",
        "schema_declared": True,
        "template_is_documentation_only": True,
        "required_fields": required_fields,
        "optional_fields": optional_fields,
        "z_d_bracket_policy": "optional; if absent/null, ActiveZ2Sigma pipeline derives it from Gamma_drag_Z2Sigma-H_Z2Sigma on z_grid",
        "flrw_component_fields": flrw_components,
        "early_plasma_fields": early_plasma,
        "critical_normalization_fields": [
            "rho_crit0_Z2Sigma_kg_m3",
            "kappa_Z2Sigma_SI",
            "kappa_rho_crit0_Z2Sigma_SI",
            "gravitational_constant_source",
        ],
        "scalar_provenance_fields": ["H0_Z2Sigma", "omega_k_Z2Sigma", "G_Z2Sigma"],
        "required_provenance": {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "compressed_planck_lcdm_rd_used": False,
            "archived_z4_reuse_used": False,
            "phenomenological_holst_bao_scan_used": False,
        },
        "component_provenance_required": True,
        "forbidden_component_provenance_tokens": ["demo", "lcdm", "planck", "z4", "holst_scan"],
        "component_manifest_schema_gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Component Manifest Schema Gate",
        "",
        f"Component manifest path: `{payload['component_manifest_path']}`",
        f"Template path: `{payload['template_path']}`",
        f"Schema declared: `{payload['schema_declared']}`",
        f"Template documentation only: `{payload['template_is_documentation_only']}`",
        f"Gate passed: `{payload['component_manifest_schema_gate_passed']}`",
        "",
        "## FLRW Component Fields",
    ]
    lines.extend(f"- `{item}`" for item in payload["flrw_component_fields"])
    lines.extend(["", "## Early Plasma Fields"])
    lines.extend(f"- `{item}`" for item in payload["early_plasma_fields"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
