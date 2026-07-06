from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_normal_flux_cancellation_gate import (
    build_payload as build_bulk_stress_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_torsion_flux_zero_or_equivariance_gate import (
    build_payload as build_holst_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_normal_matter_current_gate import (
    build_payload as build_normal_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_perfect_fluid_tangential_flux_zero_gate import (
    build_payload as build_perfect_fluid_flux_payload,
)


GRID_SOURCE_PATH = Path("outputs/active_z2_sigma/flrw_component_inputs_without_matter_flux.json")
GRID_FALLBACK_PATH = Path("outputs/active_z2_sigma/holst_nieh_yan_components.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/matter_flux_transparency_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_transparency_input_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_transparency_input_writer_gate.json")


def _load_grid(path: Path) -> list[float]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Grid source active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Grid source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return list(payload["a_grid"])


def build_payload(
    *,
    grid_source_path: Path = GRID_SOURCE_PATH,
    grid_fallback_path: Path = GRID_FALLBACK_PATH,
    output_path: Path = OUTPUT_PATH,
    normal_current_payload: dict | None = None,
    bulk_stress_payload: dict | None = None,
    perfect_fluid_flux_payload: dict | None = None,
    holst_flux_payload: dict | None = None,
) -> dict:
    normal_current = normal_current_payload or build_normal_current_payload()
    bulk_stress = bulk_stress_payload or build_bulk_stress_payload()
    perfect_fluid_flux = perfect_fluid_flux_payload or build_perfect_fluid_flux_payload()
    holst_flux = holst_flux_payload or build_holst_flux_payload()
    grid_source_exists = grid_source_path.exists()
    grid_fallback_exists = grid_fallback_path.exists()
    selected_grid_source = grid_source_path if grid_source_exists else grid_fallback_path
    selected_grid_source_exists = selected_grid_source.exists()
    no_normal_current_ready = normal_current["closure"]["no_normal_matter_current_derived"]
    normal_current_gate_ready = normal_current.get(
        "no_normal_matter_current_ready",
        no_normal_current_ready,
    )
    bulk_flux_zero_ready = (
        bulk_stress["closure"]["Z2_flux_cancellation_derived"]
        or bulk_stress["closure"]["bulk_stress_normal_projection_zero_derived"]
    )
    bulk_projection_ready = bulk_stress.get("bulk_stress_normal_flux_projection_ready", False)
    bulk_cancellation_ready = bulk_stress.get(
        "bulk_stress_normal_flux_cancellation_ready",
        bulk_flux_zero_ready,
    )
    full_bulk_transparency_ready = (
        no_normal_current_ready
        and normal_current_gate_ready
        and bulk_projection_ready
        and bulk_cancellation_ready
        and bulk_flux_zero_ready
    )
    perfect_fluid_flux_zero_ready = bool(
        perfect_fluid_flux.get("perfect_fluid_tangential_flux_zero_ready")
        or perfect_fluid_flux.get("gate_passed")
    )
    holst_boundary_flux_zero_ready = bool(
        holst_flux.get("holst_torsion_flux_zero_or_equivariance_ready")
        or holst_flux.get("gate_passed")
    )
    local_sigma_flux_slot_ready = (
        perfect_fluid_flux_zero_ready and holst_boundary_flux_zero_ready
    )
    transparency_ready = full_bulk_transparency_ready or local_sigma_flux_slot_ready
    transparency_provenance = (
        "active no-normal-current plus active bulk-stress normal-flux cancellation"
        if full_bulk_transparency_ready
        else "active perfect-fluid tangential flux zero plus local Holst/Nieh-Yan boundary flux zero"
    )
    transparency_scope = (
        "full_bulk_projection"
        if full_bulk_transparency_ready
        else "local_Sigma_flux_slot"
    )
    output_written = False
    validation_error = None
    if selected_grid_source_exists and transparency_ready:
        try:
            a_grid = _load_grid(selected_grid_source)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "active_sigma_transparency_derived": True,
                        "a_grid": a_grid,
                        "transparency_scope": transparency_scope,
                        "transparency_provenance": transparency_provenance,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-matter-flux-transparency-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "grid_source_manifest": str(grid_source_path),
        "grid_fallback_manifest": str(grid_fallback_path),
        "selected_grid_source_manifest": str(selected_grid_source),
        "output_manifest": str(output_path),
        "grid_source_exists": grid_source_exists,
        "grid_fallback_exists": grid_fallback_exists,
        "selected_grid_source_exists": selected_grid_source_exists,
        "no_normal_matter_current_ready": no_normal_current_ready,
        "normal_matter_current_gate_ready": normal_current_gate_ready,
        "bulk_stress_projection_ready": bulk_projection_ready,
        "bulk_stress_cancellation_ready": bulk_cancellation_ready,
        "bulk_stress_flux_zero_ready": bulk_flux_zero_ready,
        "perfect_fluid_flux_zero_ready": perfect_fluid_flux_zero_ready,
        "holst_boundary_flux_zero_ready": holst_boundary_flux_zero_ready,
        "full_bulk_transparency_ready": full_bulk_transparency_ready,
        "local_sigma_flux_slot_ready": local_sigma_flux_slot_ready,
        "transparency_scope": transparency_scope if transparency_ready else "none",
        "upstream_frontiers": {
            "normal_matter_current": {
                "gate": normal_current.get("status", "injected-normal-current-payload"),
                "ready": normal_current_gate_ready,
                "no_normal_current_derived": no_normal_current_ready,
                "closure": normal_current.get("closure", {}),
            },
            "bulk_stress_normal_flux": {
                "gate": bulk_stress.get("status", "injected-bulk-stress-payload"),
                "projection_ready": bulk_projection_ready,
                "cancellation_ready": bulk_cancellation_ready,
                "closure": bulk_stress.get("closure", {}),
            },
            "perfect_fluid_tangential_flux": {
                "gate": perfect_fluid_flux.get(
                    "status", "injected-perfect-fluid-flux-payload"
                ),
                "ready": perfect_fluid_flux_zero_ready,
            },
            "holst_torsion_flux": {
                "gate": holst_flux.get("status", "injected-holst-flux-payload"),
                "ready": holst_boundary_flux_zero_ready,
                "scope": holst_flux.get("scope", {}),
            },
        },
        "nearest_transparency_input_frontier": {
            "blocks": [
                "active_no_normal_matter_current_or_perfect_fluid_tangential_flux_zero",
                "active_bulk_stress_normal_flux_zero_or_local_Holst_boundary_flux_zero",
                "active_a_grid_from_non_matter_FLRW_inputs",
                "or_active_a_grid_from_Holst_zero_component",
            ],
            "diagnostic_only": True,
        },
        "active_sigma_transparency_derived": transparency_ready,
        "transparency_input_written": output_written,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "derive_no_normal_matter_current_or_perfect_fluid_tangential_flux_zero_at_Sigma",
            "derive_bulk_stress_flux_cancellation_or_local_Holst_boundary_flux_zero",
            "supply_active_grid_from_flrw_without_matter_or_holst_zero_component",
            "run_matter_flux_zero_component_from_transparency_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Transparency Input Writer Gate",
        "",
        f"Grid source exists: `{payload['grid_source_exists']}`",
        f"No-normal-current ready: `{payload['no_normal_matter_current_ready']}`",
        f"Bulk-stress flux zero ready: `{payload['bulk_stress_flux_zero_ready']}`",
        f"Transparency input written: `{payload['transparency_input_written']}`",
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
