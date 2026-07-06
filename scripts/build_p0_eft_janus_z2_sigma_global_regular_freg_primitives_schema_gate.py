from __future__ import annotations

import json
from pathlib import Path


SCHEMA_PATH = Path("outputs/schemas/global_regular_freg_primitives.schema.json")
TEMPLATE_PATH = Path("outputs/templates/global_regular_freg_primitives.template.md")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_primitives_schema_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_primitives_schema_gate.json")


def build_schema() -> dict:
    array = {"type": "array"}
    provenance = {"type": "string", "minLength": 1, "not": {"pattern": "(?i)(planck|lcdm|z4|fit|bao_scan)"}}
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "title": "Janus Z2/Sigma global regular F_reg primitives",
        "type": "object",
        "additionalProperties": False,
        "required": [
            "active_core",
            "source",
            "compressed_planck_lcdm_used",
            "archived_z4_reuse_used",
            "observational_fit_used",
            "torus_replacement_used",
            "full_no_fit_prediction_ready",
            "lambda_grid",
            "collar_coordinate_u_grid",
            "normal_connection_omega_perp_lambda_u",
            "deck_frame_map_lambda",
            "h_plus_endpoint_lambda",
            "h_minus_endpoint_lambda",
            "tau_Z2_pullback_matrix_on_endpoint_tangents",
            "endpoint_metric_norm",
            "S_Sigma_divergence_lambda",
            "bulk_normal_flux_jump_lambda",
            "surface_vector_norm",
            "primitive_provenance",
        ],
        "properties": {
            "active_core": {"const": "Z2_tunnel_Sigma"},
            "source": {"const": "active_global_regularity_primitives"},
            "compressed_planck_lcdm_used": {"const": False},
            "archived_z4_reuse_used": {"const": False},
            "observational_fit_used": {"const": False},
            "torus_replacement_used": {"const": False},
            "full_no_fit_prediction_ready": {"const": False},
            "lambda_grid": array,
            "collar_coordinate_u_grid": array,
            "normal_connection_omega_perp_lambda_u": array,
            "deck_frame_map_lambda": array,
            "h_plus_endpoint_lambda": array,
            "h_minus_endpoint_lambda": array,
            "tau_Z2_pullback_matrix_on_endpoint_tangents": array,
            "endpoint_metric_norm": array,
            "S_Sigma_divergence_lambda": array,
            "bulk_normal_flux_jump_lambda": array,
            "surface_vector_norm": array,
            "root_tolerance": {"type": "number", "exclusiveMinimum": 0},
            "primitive_provenance": {
                "type": "object",
                "additionalProperties": False,
                "required": [
                    "normal_connection_omega_perp_lambda_u",
                    "endpoint_collar_metrics_and_z2_pullback",
                    "sigma_stress_and_bulk_normal_flux",
                ],
                "properties": {
                    "normal_connection_omega_perp_lambda_u": provenance,
                    "endpoint_collar_metrics_and_z2_pullback": provenance,
                    "sigma_stress_and_bulk_normal_flux": provenance,
                },
            },
        },
    }


def build_payload(*, schema_path: Path = SCHEMA_PATH, template_path: Path = TEMPLATE_PATH) -> dict:
    schema = build_schema()
    schema_path.parent.mkdir(parents=True, exist_ok=True)
    template_path.parent.mkdir(parents=True, exist_ok=True)
    schema_path.write_text(json.dumps(schema, indent=2), encoding="utf-8")
    template_path.write_text(
        "\n".join(
            [
                "# Global Regular F_reg Primitives Template",
                "",
                "Create `outputs/active_z2_sigma/global_regular_freg_primitives.json` from active collar geometry.",
                "",
                "- `lambda_grid = R_Sigma/ell_collar`",
                "- `normal_connection_omega_perp_lambda_u[lambda,u,d,d]`",
                "- `deck_frame_map_lambda[lambda,d,d]` for the projective Z2 frame closure",
                "- endpoint metrics `h_plus_endpoint_lambda`, `h_minus_endpoint_lambda`",
                "- `tau_Z2_pullback_matrix_on_endpoint_tangents`",
                "- `S_Sigma_divergence_lambda` and `bulk_normal_flux_jump_lambda`",
                "- no Planck/LCDM/Z4/fit/BAO-scan provenance",
                "- no torus replacement",
                "",
                "The template is not an executable manifest.",
            ]
        ),
        encoding="utf-8",
    )
    return {
        "status": "janus-z2-sigma-global-regular-freg-primitives-schema-gate",
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
                "# Janus Z2/Sigma Global Regular F_reg Primitives Schema Gate",
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
