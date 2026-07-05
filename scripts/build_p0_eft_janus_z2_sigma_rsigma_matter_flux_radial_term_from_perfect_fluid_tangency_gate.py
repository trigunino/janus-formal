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
from scripts.build_p0_eft_janus_z2_sigma_perfect_fluid_tangential_flux_zero_gate import (
    build_payload as build_perfect_fluid_flux_payload,
)


A_GRID_PATH = Path("outputs/active_z2_sigma/rsigma_a_grid_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json")
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_perfect_fluid_tangency_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_perfect_fluid_tangency_gate.json"
)


def _load_grid(path: Path) -> list[float]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("a_grid active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("a_grid source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    grid = [float(value) for value in payload["a_grid"]]
    if len(grid) < 2 or any(value <= 0.0 for value in grid):
        raise ValueError("a_grid must contain at least two positive points")
    if any(b <= a for a, b in zip(grid, grid[1:])):
        raise ValueError("a_grid must be strictly increasing")
    return grid


def build_payload(
    *,
    a_grid_path: Path = A_GRID_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    perfect_fluid = build_perfect_fluid_flux_payload()
    input_exists = a_grid_path.exists()
    output_written = False
    validation_error = None
    if input_exists and perfect_fluid["perfect_fluid_tangential_flux_zero_ready"]:
        try:
            a_grid = _load_grid(a_grid_path)
            term = build_active_z2sigma_rsigma_radial_term_payload(
                term_name="E_matterFlux",
                a_grid=a_grid,
                term_values=[0.0 for _ in a_grid],
                term_provenance=(
                    "perfect-fluid tangential identity: u.n=0 and e_a.n=0 imply "
                    "T_munu e_a^mu n^nu=0 sector by sector"
                ),
            )
            write_active_z2sigma_rsigma_radial_term_manifest(output_path, term)
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rsigma-matter-flux-radial-term-from-perfect-fluid-tangency-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(a_grid_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "perfect_fluid_tangential_flux_zero_ready": perfect_fluid[
            "perfect_fluid_tangential_flux_zero_ready"
        ],
        "active_sigma_transparency_claimed": False,
        "E_matterFlux_zero_from_perfect_fluid_tangency_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none"
        if output_written
        else (
            perfect_fluid["primary_blocker"]
            if input_exists
            else "rsigma_a_grid_inputs"
        ),
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "pass_perfect_fluid_tangential_flux_zero_gate",
            "provide_outputs_active_z2_sigma_rsigma_a_grid_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Matter-Flux Radial Term From Perfect-Fluid Tangency Gate",
        "",
        f"Output written: `{payload['E_matterFlux_zero_from_perfect_fluid_tangency_written']}`",
        f"Active Sigma transparency claimed: `{payload['active_sigma_transparency_claimed']}`",
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
