from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_rho_plus0_abs_symbolic_closure_gate import (
    build_payload as rho_plus0_abs,
)
from scripts.build_p0_eft_janus_z2_exact_solution_alpha_state_sector_gate import (
    build_payload as alpha_state_sector,
)
from scripts.build_p0_eft_janus_z2_exact_solution_alpha_to_global_energy_gate import (
    build_payload as alpha_to_global_energy,
)
from scripts.build_p0_eft_janus_z2_published_global_energy_constant_route_gate import (
    build_payload as global_energy_normalization,
)
from scripts.build_p0_eft_janus_z2_sector_density_pressure_from_rho_plus0_abs_gate import (
    build_payload as density_pressure,
)
from scripts.build_p0_eft_janus_z2_sigma_sector_perfect_fluid_on_sigma_input_writer_gate import (
    build_payload as perfect_fluid,
)
from scripts.build_p0_eft_janus_z2_bimetric_bulk_to_sigma_flux_input_assembler import (
    build_payload as flux_input,
)
from scripts.build_p0_eft_janus_z2_bimetric_bulk_to_sigma_stress_flux_runner import (
    build_payload as stress_flux,
)


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_bimetric_sigma_transfer_pipeline.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_bimetric_sigma_transfer_pipeline.md")


def _stage(name: str, payload: dict[str, Any], ready_key: str = "gate_passed") -> dict[str, Any]:
    ready = bool(payload.get(ready_key))
    return {
        "name": name,
        "ready": ready,
        "status": payload.get("status"),
        "blocked_by": payload.get("blocked_by")
        or payload.get("validation_errors")
        or payload.get("validation_error")
        or payload.get("primary_blocker"),
    }


def _density_normalization_stage(
    rho: dict[str, Any],
    alpha_state: dict[str, Any],
    alpha_energy: dict[str, Any],
    global_energy: dict[str, Any],
) -> dict[str, Any]:
    local_ready = bool(rho.get("rho_plus0_abs_ready"))
    global_ready = bool(global_energy.get("global_energy_constant_route_ready"))
    return {
        "name": "density_normalization",
        "ready": local_ready or global_ready,
        "status": "janus-z2-density-normalization-route-selector",
        "routes": {
            "local_N_occ_R_curv": {
                "ready": local_ready,
                "blocked_by": rho.get("validation_errors"),
            },
            "published_alpha_global_energy": {
                "ready": global_ready,
                "alpha_state_sector_ready": bool(alpha_state.get("alpha_state_sector_ready")),
                "alpha_to_energy_ready": bool(alpha_energy.get("alpha_to_global_energy_ready")),
                "blocked_by": {
                    "alpha_state_sector": alpha_state.get("validation_errors"),
                    "alpha_to_energy": alpha_energy.get("validation_errors"),
                    "global_energy": global_energy.get("validation_errors"),
                },
            },
        },
        "blocked_by": []
        if (local_ready or global_ready)
        else [
            "local route missing N_occ_Z2Sigma/R_curv_Z2Sigma",
            "global route missing alpha_m or E_global_J",
        ],
    }


def build_payload() -> dict[str, Any]:
    rho = rho_plus0_abs(write_output=True)
    alpha_state = alpha_state_sector(write_output=True)
    alpha_energy = alpha_to_global_energy(write_output=True)
    global_energy = global_energy_normalization(write_output=True)
    dens = density_pressure(write_output=True)
    fluid = perfect_fluid()
    assembled = flux_input(write_output=True)
    flux = stress_flux(write_output=True)
    stages = [
        _density_normalization_stage(rho, alpha_state, alpha_energy, global_energy),
        _stage("rho_plus0_abs", rho, "rho_plus0_abs_ready"),
        _stage("alpha_state_sector", alpha_state, "alpha_state_sector_ready"),
        _stage("alpha_to_global_energy", alpha_energy, "alpha_to_global_energy_ready"),
        _stage("global_energy_sector_normalization", global_energy, "global_energy_constant_route_ready"),
        _stage("sector_density_pressure_on_sigma", dens, "sector_density_pressure_on_sigma_ready"),
        _stage("sector_perfect_fluid_on_sigma", fluid),
        _stage("bimetric_bulk_to_sigma_flux_input", assembled, "assembled_input_ready"),
        _stage("bimetric_bulk_to_sigma_stress_flux", flux, "sigma_stress_flux_projection_ready"),
    ]
    first_blocker = next((stage for stage in stages if not stage["ready"]), None)
    return {
        "status": "janus-z2-bimetric-sigma-transfer-pipeline",
        "active_core": "Z2_tunnel_Sigma",
        "pipeline_ready": first_blocker is None,
        "first_blocker": first_blocker,
        "stages": stages,
        "interpretation": (
            "The bimetric transfer to Sigma is a data pipeline, not a new source. "
            "It becomes physical only when density normalization, active embedding "
            "geometry, and radial variation weights are all active-derived. Density "
            "normalization may come either from local N_occ/R_curv or from the "
            "published alpha -> global-energy route."
        ),
        "no_rustine_policy": {
            "no_observational_density_fit": True,
            "no_rho_eff_collapse": True,
            "no_sigma_counterterm_source_invented": True,
            "no_legacy_z4_reuse": True,
        },
        "gate_passed": first_blocker is None,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Bimetric Sigma Transfer Pipeline",
        "",
        f"Pipeline ready: `{payload['pipeline_ready']}`",
        f"First blocker: `{payload['first_blocker']}`",
        "",
        "## Stages",
    ]
    lines.extend(f"- `{stage['name']}`: `{stage['ready']}`" for stage in payload["stages"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
