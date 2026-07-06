from __future__ import annotations

import json
from pathlib import Path


SCHEMA_PATH = Path("outputs/schemas/global_regular_freg_components.schema.json")
TEMPLATE_PATH = Path("outputs/templates/global_regular_freg_components.template.md")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_components_schema_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_global_regular_freg_components_schema_gate.json"
)


def build_schema() -> dict:
    array = {"type": "array", "items": {"type": "number"}}
    provenance = {
        "type": "string",
        "minLength": 1,
        "not": {"pattern": "(?i)(planck|lcdm|z4|fit|bao_scan)"},
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "title": "Janus Z2/Sigma global regular F_reg components",
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
            "normal_frame_holonomy_defect",
            "collar_endpoint_mismatch",
            "junction_bianchi_defect",
            "component_provenance",
        ],
        "properties": {
            "active_core": {"const": "Z2_tunnel_Sigma"},
            "source": {"const": "active_global_regularity_components"},
            "compressed_planck_lcdm_used": {"const": False},
            "archived_z4_reuse_used": {"const": False},
            "observational_fit_used": {"const": False},
            "torus_replacement_used": {"const": False},
            "full_no_fit_prediction_ready": {"const": False},
            "lambda_grid": array,
            "normal_frame_holonomy_defect": array,
            "collar_endpoint_mismatch": array,
            "junction_bianchi_defect": array,
            "root_tolerance": {"type": "number", "exclusiveMinimum": 0},
            "component_provenance": {
                "type": "object",
                "additionalProperties": False,
                "required": [
                    "normal_frame_holonomy_defect",
                    "collar_endpoint_mismatch",
                    "junction_bianchi_defect",
                ],
                "properties": {
                    "normal_frame_holonomy_defect": provenance,
                    "collar_endpoint_mismatch": provenance,
                    "junction_bianchi_defect": provenance,
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
                "# Global Regular F_reg Components Template",
                "",
                "Create `outputs/active_z2_sigma/global_regular_freg_components.json` with active geometric defects only.",
                "",
                "- `source = active_global_regularity_components`",
                "- `full_no_fit_prediction_ready = false`",
                "- no Planck/LCDM/Z4/fit/BAO-scan provenance",
                "- no torus replacement",
                "- aligned arrays over positive increasing `lambda_grid = R_Sigma/ell_collar`",
                "",
                "Required component arrays:",
                "",
                "- `normal_frame_holonomy_defect` from active collar normal connection",
                "- `collar_endpoint_mismatch` from Z2 deck pullback of endpoint collar metrics",
                "- `junction_bianchi_defect` from Sigma stress and bulk normal-flux residual",
                "",
                "The template is not an executable manifest.",
            ]
        ),
        encoding="utf-8",
    )
    return {
        "status": "janus-z2-sigma-global-regular-freg-components-schema-gate",
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
                "# Janus Z2/Sigma Global Regular F_reg Components Schema Gate",
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
