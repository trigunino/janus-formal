from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
FLUID_PATH = BASE / "sector_perfect_fluid_on_sigma_inputs.json"
EMBEDDING_PATH = BASE / "active_tunnel_embedding_geometry_inputs.json"
RADIAL_WEIGHTS_PATH = BASE / "radial_variation_tangent_weights_inputs.json"
OUTPUT_PATH = BASE / "bimetric_bulk_to_sigma_stress_flux_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_bimetric_bulk_to_sigma_flux_input_assembler.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_bimetric_bulk_to_sigma_flux_input_assembler.json")


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _check(payload: dict[str, Any], label: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{label} source must be active_derived")
    for key in [
        "observational_fit_used",
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is True:
            raise ValueError(f"{label} forbidden flag is true: {key}")


def _grid(payload: dict[str, Any]) -> list[float]:
    return [float(x) for x in payload["a_grid"]]


def _aligned(reference: list[float], payload: dict[str, Any], label: str) -> None:
    if _grid(payload) != reference:
        raise ValueError(f"{label} a_grid must match fluid a_grid")


def build_payload(
    *,
    fluid_path: Path = FLUID_PATH,
    embedding_path: Path = EMBEDDING_PATH,
    radial_weights_path: Path = RADIAL_WEIGHTS_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = True,
) -> dict[str, Any]:
    fluid = _read(fluid_path)
    embedding = _read(embedding_path)
    radial = _read(radial_weights_path)
    errors: list[str] = []
    output = None
    try:
        if fluid is None:
            errors.append("missing_sector_perfect_fluid_on_sigma_inputs")
        if embedding is None:
            errors.append("missing_active_tunnel_embedding_geometry_inputs")
        if radial is None:
            errors.append("missing_radial_variation_tangent_weights_inputs")
        if not errors:
            assert fluid is not None and embedding is not None and radial is not None
            _check(fluid, "fluid")
            _check(embedding, "embedding")
            _check(radial, "radial")
            grid = _grid(fluid)
            _aligned(grid, embedding, "embedding")
            _aligned(grid, radial, "radial")
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "observational_fit_used": False,
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "a_grid": grid,
                "rho_plus_values": fluid["rho_plus_values"],
                "p_plus_values": fluid["p_plus_values"],
                "rho_minus_values": fluid["rho_minus_values"],
                "p_minus_values": fluid["p_minus_values"],
                "metric_plus_munu_values": fluid["metric_plus_munu_values"],
                "metric_minus_munu_values": fluid["metric_minus_munu_values"],
                "u_plus_contravariant_values": fluid["u_plus_contravariant_values"],
                "u_minus_contravariant_values": fluid["u_minus_contravariant_values"],
                "tangent_vectors_values": embedding["tangent_frames_plus"],
                "normal_plus_values": embedding["unit_normals_plus"],
                "normal_minus_values": embedding["unit_normals_minus"],
                "radial_variation_tangent_weights": radial["radial_variation_tangent_weights"],
                "eps_Z2": float(embedding["z2_orientation_sign"]),
                "fluid_source": str(fluid_path),
                "embedding_source": str(embedding_path),
                "radial_weights_source": str(radial_weights_path),
            }
            if write_output:
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
    except Exception as exc:
        errors.append(str(exc))
    ready = output is not None and not errors
    return {
        "status": "janus-z2-bimetric-bulk-to-sigma-flux-input-assembler",
        "active_core": "Z2_tunnel_Sigma",
        "fluid_exists": fluid is not None,
        "embedding_exists": embedding is not None,
        "radial_weights_exists": radial is not None,
        "assembled_input_ready": ready,
        "output_path": str(output_path),
        "blocked_by": errors,
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Bimetric Bulk To Sigma Flux Input Assembler",
                "",
                f"Assembled input ready: `{payload['assembled_input_ready']}`",
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
