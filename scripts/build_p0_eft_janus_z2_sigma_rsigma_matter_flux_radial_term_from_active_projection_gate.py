from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from janus_lab.z2_sigma_rsigma_radial_terms import (
    build_active_z2sigma_rsigma_radial_term_payload,
    write_active_z2sigma_rsigma_radial_term_manifest,
)


INPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_active_projection_radial_inputs.json")
TRANSPARENCY_INPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_transparency_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_active_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_active_projection_gate.json")


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("active projection active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("active projection source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    if payload.get("active_flux_projection_ready") is not True:
        raise ValueError("active_flux_projection_ready must be true")
    if payload.get("matter_flux_radial_reduction_ready") is not True:
        raise ValueError("matter_flux_radial_reduction_ready must be true")
    if payload.get("selected_route") != "active_projection":
        raise ValueError("selected_route must be active_projection")
    return payload


def _transparency_route_already_derived(path: Path) -> bool:
    if not path.exists():
        return False
    payload = json.loads(path.read_text(encoding="utf-8"))
    return (
        payload.get("active_core") == "Z2_tunnel_Sigma"
        and payload.get("source") == "active_derived"
        and payload.get("active_sigma_transparency_derived") is True
    )


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    transparency_input_path: Path = TRANSPARENCY_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = input_path.exists()
    transparency_route_derived = _transparency_route_already_derived(transparency_input_path)
    output_written = False
    validation_error = None
    if input_exists and not transparency_route_derived:
        try:
            source = _load_input(input_path)
            term = build_active_z2sigma_rsigma_radial_term_payload(
                term_name="E_matterFlux",
                a_grid=source["a_grid"],
                term_values=source["E_matterFlux_values"],
                term_provenance=(
                    "active projected matter flux radial block from F_a^Z2Sigma(a)"
                ),
            )
            write_active_z2sigma_rsigma_radial_term_manifest(output_path, term)
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    elif input_exists and transparency_route_derived:
        validation_error = "active Sigma transparency route already derived; active projection writer is route-exclusive"
    return {
        "status": "janus-z2-sigma-rsigma-matter-flux-radial-term-from-active-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "transparency_route_already_derived": transparency_route_derived,
        "E_matterFlux_from_active_projection_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_projected_matter_flux_radial_manifest",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_F_a_Z2Sigma_of_a_from_active_bulk_stress_tangents_normals",
            "reduce_projected_flux_to_E_matterFlux_values",
            "write_outputs_active_z2_sigma_matter_flux_active_projection_radial_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Matter-Flux Radial Term From Active Projection Gate",
        "",
        f"Output written: `{payload['E_matterFlux_from_active_projection_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
