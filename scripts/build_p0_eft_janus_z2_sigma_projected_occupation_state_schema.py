from __future__ import annotations

import json
from pathlib import Path


SCHEMA_PATH = Path("outputs/schemas/projected_occupation_state_inputs.schema.json")
TEMPLATE_PATH = Path("outputs/templates/projected_occupation_state_inputs.template.md")
EXAMPLE_PATH = Path("outputs/examples/projected_occupation_state_inputs.example.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projected_occupation_state_schema.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projected_occupation_state_schema.json"
)


def build_schema() -> dict:
    clean_source = {
        "type": "string",
        "minLength": 1,
        "not": {"pattern": "(?i)(planck|lcdm|z4|fit|bao_scan)"},
    }
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "title": "Janus Z2/Sigma projected occupation state input",
        "type": "object",
        "additionalProperties": False,
        "required": [
            "active_core",
            "source",
            "full_no_fit_prediction_ready",
            "N_occ_Z2Sigma",
            "N_occ_provenance",
        ],
        "properties": {
            "active_core": {"const": "Z2_tunnel_Sigma"},
            "source": {"const": "explicit_state_initial_data"},
            "full_no_fit_prediction_ready": {"const": False},
            "N_occ_Z2Sigma": {"type": "number", "exclusiveMinimum": 0},
            "N_occ_provenance": clean_source,
        },
    }


def build_payload(
    *,
    schema_path: Path = SCHEMA_PATH,
    template_path: Path = TEMPLATE_PATH,
    example_path: Path = EXAMPLE_PATH,
) -> dict:
    schema = build_schema()
    schema_path.parent.mkdir(parents=True, exist_ok=True)
    template_path.parent.mkdir(parents=True, exist_ok=True)
    example_path.parent.mkdir(parents=True, exist_ok=True)
    schema_path.write_text(json.dumps(schema, indent=2), encoding="utf-8")
    example = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "explicit_state_initial_data",
        "full_no_fit_prediction_ready": False,
        "N_occ_Z2Sigma": 1.0,
        "N_occ_provenance": "example_declared_superselection_state_initial_data_not_active",
    }
    example_path.write_text(json.dumps(example, indent=2), encoding="utf-8")
    template_path.write_text(
        "\n".join(
            [
                "# Projected Occupation State Input Template",
                "",
                "Create `outputs/active_z2_sigma/projected_occupation_state_inputs.json` only if an explicit state input is intended.",
                "",
                "This is not a no-fit theorem. It supplies the open superselection datum `N_occ` after Z2/Noether reduction.",
                "",
                "```json",
                "{",
                '  "active_core": "Z2_tunnel_Sigma",',
                '  "source": "explicit_state_initial_data",',
                '  "full_no_fit_prediction_ready": false,',
                '  "N_occ_Z2Sigma": 0.0,',
                '  "N_occ_provenance": "declared_superselection_state_initial_data"',
                "}",
                "```",
                "",
                "The value must be positive. Provenance must not use Planck, LCDM, Z4, fit, or BAO scan inputs.",
            ]
        ),
        encoding="utf-8",
    )
    return {
        "status": "janus-z2-sigma-projected-occupation-state-schema",
        "active_core": "Z2_tunnel_Sigma",
        "schema_path": str(schema_path),
        "template_path": str(template_path),
        "example_path": str(example_path),
        "schema_written": True,
        "template_written": True,
        "example_written": True,
        "writes_active_manifest": False,
        "example_is_active_manifest": False,
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
                "# Janus Z2/Sigma Projected Occupation State Schema",
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
