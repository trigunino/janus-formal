from __future__ import annotations

import json
from pathlib import Path


SCHEMA_PATH = Path("outputs/schemas/normal_connection_frame_primitives.schema.json")
TEMPLATE_PATH = Path("outputs/templates/normal_connection_frame_primitives.template.md")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_connection_frame_primitives_schema_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_normal_connection_frame_primitives_schema_gate.json")


def build_schema() -> dict:
    array = {"type": "array"}
    provenance = {"type": "string", "minLength": 1, "not": {"pattern": "(?i)(planck|lcdm|z4|fit|bao_scan)"}}
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "title": "Janus Z2/Sigma normal connection frame primitives",
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
            "normal_frame_basis_lambda_u",
            "partial_u_normal_frame_basis_lambda_u",
            "connection_u_matrix_lambda_u",
            "ambient_metric_lambda_u",
            "primitive_provenance",
        ],
        "properties": {
            "active_core": {"const": "Z2_tunnel_Sigma"},
            "source": {"const": "active_normal_frame_connection_primitives"},
            "compressed_planck_lcdm_used": {"const": False},
            "archived_z4_reuse_used": {"const": False},
            "observational_fit_used": {"const": False},
            "torus_replacement_used": {"const": False},
            "full_no_fit_prediction_ready": {"const": False},
            "lambda_grid": array,
            "collar_coordinate_u_grid": array,
            "normal_frame_basis_lambda_u": array,
            "partial_u_normal_frame_basis_lambda_u": array,
            "connection_u_matrix_lambda_u": array,
            "ambient_metric_lambda_u": array,
            "primitive_provenance": {
                "type": "object",
                "additionalProperties": False,
                "required": [
                    "normal_frame_basis_lambda_u",
                    "partial_u_normal_frame_basis_lambda_u",
                    "connection_u_matrix_lambda_u",
                    "ambient_metric_lambda_u",
                ],
                "properties": {
                    "normal_frame_basis_lambda_u": provenance,
                    "partial_u_normal_frame_basis_lambda_u": provenance,
                    "connection_u_matrix_lambda_u": provenance,
                    "ambient_metric_lambda_u": provenance,
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
                "# Normal Connection Frame Primitives Template",
                "",
                "Create `outputs/active_z2_sigma/normal_connection_frame_primitives.json` from active collar geometry.",
                "",
                "- `lambda_grid = R_Sigma/ell_collar`",
                "- `collar_coordinate_u_grid`",
                "- `normal_frame_basis_lambda_u[lambda,u,d_normal,d_ambient]`",
                "- `partial_u_normal_frame_basis_lambda_u[lambda,u,d_normal,d_ambient]`",
                "- `connection_u_matrix_lambda_u[lambda,u,d_ambient,d_ambient]`",
                "- `ambient_metric_lambda_u[lambda,u,d_ambient,d_ambient]`",
                "- no Planck/LCDM/Z4/fit/BAO-scan provenance",
                "- no torus replacement",
                "",
                "This template is not an executable manifest.",
            ]
        ),
        encoding="utf-8",
    )
    return {
        "status": "janus-z2-sigma-normal-connection-frame-primitives-schema-gate",
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
                "# Janus Z2/Sigma Normal Connection Frame Primitives Schema Gate",
                "",
                f"Schema written: `{payload['schema_written']}`",
                f"Template written: `{payload['template_written']}`",
                f"Writes active manifest: `{payload['writes_active_manifest']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
