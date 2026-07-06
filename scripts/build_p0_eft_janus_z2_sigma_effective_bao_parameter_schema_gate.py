from __future__ import annotations

import json
from pathlib import Path


SCHEMA_PATH = Path("outputs/schemas/effective_bao_parameter_inputs.schema.json")
TEMPLATE_PATH = Path("outputs/templates/effective_bao_parameter_inputs.template.md")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_parameter_schema_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_parameter_schema_gate.json"
)


def build_schema() -> dict:
    array = {"type": "array", "items": {"type": "number"}}
    provenance = {"type": "string", "minLength": 1, "not": {"pattern": "(?i)(planck|lcdm|z4|fit|bao_scan)"}}
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "title": "Janus Z2/Sigma effective BAO parameter inputs",
        "type": "object",
        "additionalProperties": False,
        "required": [
            "active_core",
            "source",
            "compressed_planck_lcdm_used",
            "archived_z4_reuse_used",
            "observational_fit_used",
            "full_no_fit_prediction_ready",
            "effective_initial_data",
            "effective_initial_data_provenance",
            "z_grid",
            "E_Z2Sigma",
            "c_s_over_c_Z2Sigma",
            "Gamma_drag_over_H0_Z2Sigma",
            "omega_k_Z2Sigma",
            "z_max",
            "primitive_provenance",
        ],
        "properties": {
            "active_core": {"const": "Z2_tunnel_Sigma"},
            "source": {"const": "effective_parameter_inputs"},
            "compressed_planck_lcdm_used": {"const": False},
            "archived_z4_reuse_used": {"const": False},
            "observational_fit_used": {"const": False},
            "full_no_fit_prediction_ready": {"const": False},
            "effective_initial_data": {
                "type": "object",
                "additionalProperties": False,
                "required": [
                    "R_Sigma_over_ell_collar_Z2Sigma",
                    "projected_baryon_number_charge_Z2Sigma",
                ],
                "properties": {
                    "R_Sigma_over_ell_collar_Z2Sigma": {
                        "type": "number",
                        "exclusiveMinimum": 0,
                    },
                    "projected_baryon_number_charge_Z2Sigma": {
                        "type": "number",
                        "exclusiveMinimum": 0,
                    },
                },
            },
            "effective_initial_data_provenance": {
                "type": "object",
                "additionalProperties": False,
                "required": [
                    "R_Sigma_over_ell_collar_Z2Sigma",
                    "projected_baryon_number_charge_Z2Sigma",
                ],
                "properties": {
                    "R_Sigma_over_ell_collar_Z2Sigma": provenance,
                    "projected_baryon_number_charge_Z2Sigma": provenance,
                },
            },
            "z_grid": array,
            "E_Z2Sigma": array,
            "c_s_over_c_Z2Sigma": array,
            "Gamma_drag_over_H0_Z2Sigma": array,
            "omega_k_Z2Sigma": {"type": "number"},
            "z_max": {"type": "number"},
            "z_d_bracket": {
                "anyOf": [
                    {"type": "null"},
                    {
                        "type": "array",
                        "minItems": 2,
                        "maxItems": 2,
                        "items": {"type": "number"},
                    },
                ]
            },
            "primitive_provenance": {
                "type": "object",
                "additionalProperties": False,
                "required": [
                    "E_Z2Sigma",
                    "c_s_over_c_Z2Sigma",
                    "Gamma_drag_over_H0_Z2Sigma",
                    "omega_k_Z2Sigma",
                ],
                "properties": {
                    "E_Z2Sigma": provenance,
                    "c_s_over_c_Z2Sigma": provenance,
                    "Gamma_drag_over_H0_Z2Sigma": provenance,
                    "omega_k_Z2Sigma": provenance,
                },
            },
        },
    }


def build_payload(
    *,
    schema_path: Path = SCHEMA_PATH,
    template_path: Path = TEMPLATE_PATH,
) -> dict:
    schema = build_schema()
    schema_path.parent.mkdir(parents=True, exist_ok=True)
    template_path.parent.mkdir(parents=True, exist_ok=True)
    schema_path.write_text(json.dumps(schema, indent=2), encoding="utf-8")
    template_path.write_text(
        "\n".join(
            [
                "# Effective BAO Parameter Inputs Template",
                "",
                "Create `outputs/active_z2_sigma/effective_bao_parameter_inputs.json` with:",
                "",
                "- `source = effective_parameter_inputs`",
                "- `full_no_fit_prediction_ready = false`",
                "- `R_Sigma_over_ell_collar_Z2Sigma` and `projected_baryon_number_charge_Z2Sigma`",
                "- aligned arrays: `z_grid`, `E_Z2Sigma`, `c_s_over_c_Z2Sigma`, `Gamma_drag_over_H0_Z2Sigma`",
                "- `omega_k_Z2Sigma`, `z_max`, optional `z_d_bracket`",
                "- provenance strings that do not mention Planck, LCDM, Z4, fit, or BAO scan",
                "",
                "Minimal JSON shape:",
                "",
                "```json",
                "{",
                '  "active_core": "Z2_tunnel_Sigma",',
                '  "source": "effective_parameter_inputs",',
                '  "compressed_planck_lcdm_used": false,',
                '  "archived_z4_reuse_used": false,',
                '  "observational_fit_used": false,',
                '  "full_no_fit_prediction_ready": false,',
                '  "effective_initial_data": {',
                '    "R_Sigma_over_ell_collar_Z2Sigma": 0.0,',
                '    "projected_baryon_number_charge_Z2Sigma": 0.0',
                "  },",
                '  "effective_initial_data_provenance": {',
                '    "R_Sigma_over_ell_collar_Z2Sigma": "derive_or_declare_effective_initial_data",',
                '    "projected_baryon_number_charge_Z2Sigma": "derive_or_declare_effective_initial_data"',
                "  },",
                '  "z_grid": [],',
                '  "E_Z2Sigma": [],',
                '  "c_s_over_c_Z2Sigma": [],',
                '  "Gamma_drag_over_H0_Z2Sigma": [],',
                '  "omega_k_Z2Sigma": 0.0,',
                '  "z_max": 0.0,',
                '  "z_d_bracket": null,',
                '  "primitive_provenance": {',
                '    "E_Z2Sigma": "derive_effective_background_equation",',
                '    "c_s_over_c_Z2Sigma": "derive_effective_plasma_equation",',
                '    "Gamma_drag_over_H0_Z2Sigma": "derive_effective_drag_equation",',
                '    "omega_k_Z2Sigma": "derive_effective_curvature_convention"',
                "  }",
                "}",
                "```",
                "",
                "The zeros and empty arrays above are placeholders; a real manifest must use positive, aligned arrays.",
            ]
        ),
        encoding="utf-8",
    )
    return {
        "status": "janus-z2-sigma-effective-bao-parameter-schema-gate",
        "active_core": "Z2_tunnel_Sigma",
        "schema_path": str(schema_path),
        "template_path": str(template_path),
        "schema_written": True,
        "template_written": True,
        "writes_active_manifest": False,
        "template_is_executable_manifest": False,
        "full_no_fit_prediction_ready": False,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Effective BAO Parameter Schema Gate",
                "",
                f"Schema written: `{payload['schema_written']}`",
                f"Template written: `{payload['template_written']}`",
                f"Writes active manifest: `{payload['writes_active_manifest']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
