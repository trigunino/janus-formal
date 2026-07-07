from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_matter_flux import (
    build_active_matter_flux_projection_payload,
    build_bulk_stress_on_sigma_payload,
)


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "bimetric_bulk_to_sigma_stress_flux_inputs.json"
STRESS_OUTPUT_PATH = BASE / "bimetric_bulk_stress_on_sigma_inputs.json"
FLUX_OUTPUT_PATH = BASE / "bimetric_bulk_to_sigma_stress_flux_projection.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_bimetric_bulk_to_sigma_stress_flux_runner.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_bimetric_bulk_to_sigma_stress_flux_runner.json")


FORBIDDEN_FLAGS = (
    "observational_fit_used",
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "phenomenological_holst_bao_scan_used",
)


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _validate_source(source: dict[str, Any]) -> None:
    if source.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("active_core must be Z2_tunnel_Sigma")
    if source.get("source") != "active_derived":
        raise ValueError("source must be active_derived")
    for key in FORBIDDEN_FLAGS:
        if source.get(key) is True:
            raise ValueError(f"forbidden provenance flag is true: {key}")


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    stress_output_path: Path = STRESS_OUTPUT_PATH,
    flux_output_path: Path = FLUX_OUTPUT_PATH,
    write_output: bool = True,
) -> dict[str, Any]:
    source = _read(input_path)
    errors: list[str] = []
    stress_payload = None
    flux_payload = None
    if source is None:
        errors.append("missing_bimetric_bulk_to_sigma_stress_flux_inputs")
    else:
        try:
            _validate_source(source)
            stress_payload = build_bulk_stress_on_sigma_payload(source)
            flux_source = {
                **source,
                "T_plus_munu_values": stress_payload["T_plus_munu_values"],
                "T_minus_munu_values": stress_payload["T_minus_munu_values"],
            }
            flux_payload = build_active_matter_flux_projection_payload(flux_source)
            if write_output:
                stress_output_path.parent.mkdir(parents=True, exist_ok=True)
                stress_output_path.write_text(json.dumps(stress_payload, indent=2), encoding="utf-8")
                flux_output_path.write_text(json.dumps(flux_payload, indent=2), encoding="utf-8")
        except Exception as exc:
            errors.append(str(exc))
    ready = stress_payload is not None and flux_payload is not None and not errors
    return {
        "status": "janus-z2-bimetric-bulk-to-sigma-stress-flux-runner",
        "active_core": "Z2_tunnel_Sigma",
        "purpose": "Transfer active plus/minus bimetric bulk perfect-fluid stress tensors to Sigma and project T e n.",
        "input_path": str(input_path),
        "input_exists": source is not None,
        "bimetric_bulk_stress_transferred_to_sigma": ready,
        "sigma_stress_flux_projection_ready": ready,
        "stress_output_path": str(stress_output_path),
        "flux_output_path": str(flux_output_path),
        "required_input_blocks": [
            "a_grid",
            "rho_plus_values",
            "p_plus_values",
            "rho_minus_values",
            "p_minus_values",
            "metric_plus_munu_values",
            "metric_minus_munu_values",
            "u_plus_contravariant_values",
            "u_minus_contravariant_values",
            "tangent_vectors_values",
            "normal_plus_values",
            "normal_minus_values",
            "radial_variation_tangent_weights",
        ],
        "blocked_by": errors,
        "no_rustine_policy": {
            "no_rho_eff_collapse": True,
            "no_sigma_source_invented": True,
            "no_observational_density_fit": True,
            "no_legacy_z4_reuse": True,
        },
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Bimetric Bulk To Sigma Stress Flux Runner",
                "",
                f"Input exists: `{payload['input_exists']}`",
                f"Bulk stress transferred to Sigma: `{payload['bimetric_bulk_stress_transferred_to_sigma']}`",
                f"Sigma stress-flux projection ready: `{payload['sigma_stress_flux_projection_ready']}`",
                "",
                "## Blocked By",
                *[f"- `{item}`" for item in payload["blocked_by"]],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
