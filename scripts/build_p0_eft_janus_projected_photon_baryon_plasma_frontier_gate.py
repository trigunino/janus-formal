from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_physical_input_obligation_gate import (
    build_payload as build_physical_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_gate import (
    build_payload as build_scale_free_plasma_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_projected_photon_baryon_plasma_frontier_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_projected_photon_baryon_plasma_frontier_gate.json"
)


def _other_route_blockers() -> list[dict[str, Any]]:
    return [
        {
            "route": "orbifold_redshift_map",
            "frontier": "derive z_obs = F_orbifold(z_global)",
            "blocker": (
                "No photon energy transport law across Z2/Sigma has been derived. "
                "Without it, an orbifold map is only a re-labeling of redshift."
            ),
            "reopen_condition": "derive null-geodesic or boundary transport with low-z identity and high-z lift",
        },
        {
            "route": "early_time_sister_branch",
            "frontier": "derive a pre-drag H_J branch and matching law",
            "blocker": (
                "The paper-native late SN branch has finite z_max for q0=-0.087. "
                "A second branch needs a non-arbitrary matching condition."
            ),
            "reopen_condition": "derive Janus/Z2 late-to-early matching plus H_J(z) through z_d",
        },
        {
            "route": "topological_spectrum_ruler",
            "frontier": "derive a Sigma/orbifold eigen-ruler with scale and plasma coupling",
            "blocker": (
                "Topology can give periods/eigenvalues, but not yet an absolute physical ruler "
                "coupled to photon-baryon drag."
            ),
            "reopen_condition": "derive eigenproblem, absolute scale, and coupling to acoustic plasma modes",
        },
    ]


def build_payload() -> dict[str, Any]:
    physical = build_physical_input_payload()
    plasma = build_scale_free_plasma_payload()
    formula_chain = {
        "rho_baryon_history_builder_ready": True,
        "rho_photon_history_builder_ready": True,
        "sound_speed_formula_ready": True,
        "saha_ionization_builder_ready": True,
        "free_electron_density_builder_ready": True,
        "thomson_drag_formula_ready": True,
        "drag_epoch_solver_ready": True,
        "sound_ruler_integrator_ready": True,
        "bao_distance_calculator_ready": True,
    }
    missing_active_inputs = [
        "active_baryon_number_density0_m3_Z2Sigma",
        "active_rho_baryon0_Z2Sigma",
        "active_photon_temperature_or_rho_photon0_Z2Sigma",
        "active_ionization_fraction_history_or_Saha_normalization",
        "active_H0_Z2Sigma",
        "active_E_Z2Sigma_predrag",
    ]
    hard_blockers = [
        "No active early_plasma.json manifest exists.",
        "No active background_H0_inputs.json manifest exists.",
        "The model normalization manifest is missing baryon number density, ionization fraction, and electrons per baryon.",
        "The code can compute c_s, Gamma_drag, z_d and r_d after inputs, but cannot derive the inputs from the current paper-native Janus branch.",
    ]
    native_rd_ready = (
        all(formula_chain.values())
        and physical["early_plasma_physical_inputs_ready"]
        and plasma["plasma_primitive_valid"]
    )
    return {
        "status": "janus-projected-photon-baryon-plasma-frontier-gate",
        "route": "projected_photon_baryon_plasma",
        "active_core": "Z2_tunnel_Sigma",
        "formula_chain": formula_chain,
        "physical_input_obligation": {
            "gate": physical["status"],
            "passed": physical["gate_passed"],
            "codata_constants_valid": physical["codata_constants_valid"],
            "model_normalization_valid": physical["model_normalization_valid"],
            "model_normalization_missing_fields": physical[
                "model_normalization_missing_fields"
            ],
            "missing_physical_inputs": physical["missing_physical_inputs"],
        },
        "scale_free_plasma_primitive": {
            "gate": plasma["status"],
            "passed": plasma["gate_passed"],
            "input_exists": plasma["input_exists"],
            "blocker": plasma["blocker"],
        },
        "missing_active_inputs": missing_active_inputs,
        "hard_blockers": hard_blockers,
        "other_route_blockers": _other_route_blockers(),
        "native_rd_evaluated": native_rd_ready,
        "native_bao_prediction_ready": False,
        "current_bottom_reached": True,
        "next_non_rustine_step": (
            "derive active baryon/photon normalizations and active pre-drag H_J "
            "from the Janus/Z2 bulk-to-Sigma projection"
        ),
        "forbidden_shortcuts": [
            "Planck/Lambda-CDM r_d reuse",
            "observational H0 fit as native scale",
            "mock early_plasma manifest",
            "archived Z4 BAO reuse",
            "post-hoc BAO ruler rescaling",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Projected Photon-Baryon Plasma Frontier",
        "",
        f"Route: `{payload['route']}`",
        f"Native r_d evaluated: `{payload['native_rd_evaluated']}`",
        f"Native BAO prediction ready: `{payload['native_bao_prediction_ready']}`",
        f"Current bottom reached: `{payload['current_bottom_reached']}`",
        "",
        "## What is already calculable",
    ]
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in payload["formula_chain"].items()
    )
    lines.extend(
        [
            "",
            "## Hard blockers",
        ]
    )
    lines.extend(f"- {item}" for item in payload["hard_blockers"])
    lines.extend(["", "## Missing active inputs"])
    lines.extend(f"- `{item}`" for item in payload["missing_active_inputs"])
    lines.extend(["", "## Other routes remain blocked"])
    for route in payload["other_route_blockers"]:
        lines.extend(
            [
                f"### {route['route']}",
                f"- frontier: `{route['frontier']}`",
                f"- blocker: {route['blocker']}",
                f"- reopen condition: `{route['reopen_condition']}`",
                "",
            ]
        )
    lines.extend(
        [
            "## Next non-rustine step",
            "",
            payload["next_non_rustine_step"],
            "",
            "## Forbidden shortcuts",
        ]
    )
    lines.extend(f"- `{item}`" for item in payload["forbidden_shortcuts"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
