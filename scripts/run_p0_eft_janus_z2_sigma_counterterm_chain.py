from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_density_variation_input_writer_gate import (
    build_payload as write_density_variation_inputs,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_geometry_factors_from_unit_q_gate import (
    build_payload as write_geometry_factors,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_counterterm_radial_term_from_density_variation_gate import (
    build_payload as write_rsigma_counterterm,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_trace_residual_tensor_input_writer_gate import (
    build_payload as write_trace_tensors,
)
from scripts.derive_p0_eft_janus_z2_sigma_alpha_radial_components_to_trace_residual_inputs_gate import (
    build_payload as write_trace_inputs,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_immirzi_scalar_contraction_torsionless import (
    build_payload as write_immirzi_contraction,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_lct_radial_profile_from_residual_contractions import (
    build_payload as write_lct_profile,
)
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_residual_scalar_contractions import (
    build_payload as write_scalar_contractions,
)
from scripts.derive_p0_eft_janus_z2_sigma_round_throat_counterterm_symbolic_closure import (
    build_payload as write_round_throat_symbolic_counterterm,
)
from scripts.derive_p0_eft_janus_z2_sigma_round_throat_no_extension_closure import (
    build_payload as write_round_throat_no_extension_closure,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_basis_coefficient_solver_gate import (
    build_payload as write_minimal_basis_coefficients,
)
from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_active_density_coefficient_route_gate import (
    build_payload as build_coefficient_route,
)
from scripts.derive_p0_eft_janus_z2_sigma_riccati_normal_flow_to_surface_hk_geometry_gate import (
    build_payload as write_riccati_tensor_geometry,
)
from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_alpha_radial_projection_gate import (
    build_payload as write_alpha_radial_components,
)
from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_projection_input_writer_gate import (
    build_payload as write_surface_hk_projection_inputs,
)
from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_radial_geometry_input_writer_gate import (
    build_payload as write_surface_hk_radial_geometry,
)
from scripts.write_p0_eft_janus_z2_sigma_surface_hk_normal_flow_from_round_throat import (
    build_payload as write_surface_hk_normal_flow,
)
from scripts.write_p0_eft_janus_z2_sigma_surface_hk_coefficients_from_minimal_counterterm import (
    build_payload as write_surface_hk_coefficients_from_minimal,
)
from scripts.write_p0_eft_janus_z2_sigma_surface_hk_radius_grid_from_rsigma_solution import (
    build_payload as write_surface_hk_radius_grid,
)


BASE = Path("outputs/active_z2_sigma")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_chain.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_chain.json")


def _passed(payload: dict) -> bool:
    return bool(payload.get("gate_passed"))


def _blocker(payload: dict) -> str:
    if payload.get("validation_error"):
        return str(payload["validation_error"])
    if payload.get("primary_blocker"):
        return str(payload["primary_blocker"])
    missing = payload.get("next_required") or []
    if missing:
        return ", ".join(str(item) for item in missing)
    return str(payload.get("validation_error") or "unknown")


def build_payload(*, base: Path = BASE) -> dict:
    paths = {
        "q": base / "unit_intrinsic_metric_q_ab_inputs.json",
        "geometry": base / "counterterm_radial_geometry_factors.json",
        "alpha_radial": base / "counterterm_alpha_res_radial_components.json",
        "surface_hk_radius_grid": base / "surface_hk_round_throat_radius_grid_inputs.json",
        "surface_hk_normal_flow": base / "surface_hk_normal_flow_geometry_inputs.json",
        "surface_hk_tensor_geometry": base / "surface_hk_radial_tensor_geometry_inputs.json",
        "surface_hk_radial_geometry": base / "surface_hk_radial_geometry_inputs.json",
        "surface_hk_coefficients": base / "surface_hk_active_density_coefficients.json",
        "minimal_coefficients": base / "counterterm_minimal_basis_coefficients.json",
        "surface_hk_projection": base / "surface_hk_alpha_radial_projection_inputs.json",
        "trace": base / "counterterm_trace_residual_inputs.json",
        "metric_tensor": base / "counterterm_metric_residual_tensor_inputs.json",
        "extrinsic_tensor": base / "counterterm_extrinsic_residual_tensor_inputs.json",
        "holst": base / "holst_nieh_yan_radial_inputs.json",
        "e_holst": base / "rsigma_E_HolstNiehYan.json",
        "e_matter": base / "rsigma_E_matterFlux.json",
        "immirzi": base / "counterterm_immirzi_residual_scalar_inputs.json",
        "radius": base / "rsigma_radius_solution.json",
        "scalar_contractions": base / "counterterm_residual_scalar_contractions_inputs.json",
        "lct_profile": base / "counterterm_lct_radial_profile.json",
        "density_variation": base / "counterterm_radial_density_variation_inputs.json",
        "e_counterterm": base / "rsigma_E_counterterm.json",
    }
    coefficient_route = build_coefficient_route(
        coefficient_path=paths["surface_hk_coefficients"],
        trace_target_path=paths["trace"],
    )
    steps: list[dict] = []
    step_specs = [
        (
            "round_throat_counterterm_symbolic_closure",
            lambda: write_round_throat_symbolic_counterterm(
                coeff_path=paths["surface_hk_coefficients"],
                radius_path=paths["surface_hk_radius_grid"],
            ),
        ),
        (
            "round_throat_no_extension_closure",
            lambda: write_round_throat_no_extension_closure(
                holst_path=paths["e_holst"],
                matter_path=paths["e_matter"],
            ),
        ),
        (
            "counterterm_radial_geometry_factors",
            lambda: write_geometry_factors(
                q_input_path=paths["q"],
                output_path=paths["geometry"],
            ),
        ),
        (
            "counterterm_immirzi_scalar_contraction",
            lambda: write_immirzi_contraction(
                holst_path=paths["holst"],
                output_path=paths["immirzi"],
            ),
        ),
        (
            "counterterm_minimal_basis_coefficients",
            lambda: {"gate_passed": True, "status": "existing-counterterm-minimal-basis-coefficients"}
            if paths["alpha_radial"].exists()
            or paths["surface_hk_coefficients"].exists()
            or paths["minimal_coefficients"].exists()
            else write_minimal_basis_coefficients(
                trace_path=paths["trace"],
                q_path=paths["q"],
                output_path=paths["minimal_coefficients"],
            ),
        ),
        (
            "surface_hk_active_density_coefficients",
            lambda: {"gate_passed": True, "status": "existing-surface-hk-active-density-coefficients"}
            if paths["alpha_radial"].exists() or paths["surface_hk_coefficients"].exists()
            else write_surface_hk_coefficients_from_minimal(
                input_path=paths["minimal_coefficients"],
                output_path=paths["surface_hk_coefficients"],
            ),
        ),
        (
            "surface_hk_round_throat_radius_grid",
            lambda: {"gate_passed": True, "status": "existing-surface-hk-round-throat-radius-grid"}
            if paths["alpha_radial"].exists()
            or paths["surface_hk_normal_flow"].exists()
            or paths["surface_hk_radius_grid"].exists()
            else write_surface_hk_radius_grid(
                input_path=paths["radius"],
                output_path=paths["surface_hk_radius_grid"],
            ),
        ),
        (
            "surface_hk_normal_flow_geometry",
            lambda: {"gate_passed": True, "status": "existing-surface-hk-normal-flow-geometry"}
            if paths["alpha_radial"].exists() or paths["surface_hk_normal_flow"].exists()
            else write_surface_hk_normal_flow(
                q_path=paths["q"],
                radius_path=paths["surface_hk_radius_grid"],
                output_path=paths["surface_hk_normal_flow"],
            ),
        ),
        (
            "surface_hk_tensor_geometry",
            lambda: {"gate_passed": True, "status": "existing-surface-hk-tensor-geometry"}
            if paths["alpha_radial"].exists() or paths["surface_hk_tensor_geometry"].exists()
            else write_riccati_tensor_geometry(
                input_path=paths["surface_hk_normal_flow"],
                output_path=paths["surface_hk_tensor_geometry"],
            ),
        ),
        (
            "surface_hk_radial_geometry",
            lambda: {"gate_passed": True, "status": "existing-surface-hk-radial-geometry"}
            if paths["alpha_radial"].exists() or paths["surface_hk_radial_geometry"].exists()
            else write_surface_hk_radial_geometry(
                input_path=paths["surface_hk_tensor_geometry"],
                output_path=paths["surface_hk_radial_geometry"],
            ),
        ),
        (
            "surface_hk_alpha_radial_projection_inputs",
            lambda: {"gate_passed": True, "status": "existing-surface-hk-alpha-radial-projection-inputs"}
            if paths["alpha_radial"].exists() or paths["surface_hk_projection"].exists()
            else write_surface_hk_projection_inputs(
                geometry_path=paths["surface_hk_radial_geometry"],
                coefficient_path=paths["surface_hk_coefficients"],
                output_path=paths["surface_hk_projection"],
            ),
        ),
        (
            "counterterm_alpha_res_radial_components",
            lambda: {"gate_passed": True, "status": "existing-counterterm-alpha-res-radial-components"}
            if paths["alpha_radial"].exists()
            else write_alpha_radial_components(
                input_path=paths["surface_hk_projection"],
                output_path=paths["alpha_radial"],
            ),
        ),
        (
            "counterterm_trace_residual_inputs",
            lambda: {"gate_passed": True, "status": "existing-counterterm-trace-residual-inputs"}
            if paths["trace"].exists()
            else write_trace_inputs(
                input_path=paths["alpha_radial"],
                output_path=paths["trace"],
            ),
        ),
        (
            "counterterm_residual_tensors",
            lambda: write_trace_tensors(
                q_path=paths["q"],
                trace_path=paths["trace"],
                metric_output_path=paths["metric_tensor"],
                extrinsic_output_path=paths["extrinsic_tensor"],
            ),
        ),
        (
            "counterterm_residual_scalar_contractions",
            lambda: write_scalar_contractions(
                q_path=paths["q"],
                radius_path=paths["radius"],
                metric_path=paths["metric_tensor"],
                extrinsic_path=paths["extrinsic_tensor"],
                immirzi_path=paths["immirzi"],
                output_path=paths["scalar_contractions"],
            ),
        ),
        (
            "counterterm_lct_radial_profile",
            lambda: write_lct_profile(
                input_path=paths["scalar_contractions"],
                output_path=paths["lct_profile"],
                immirzi_path=paths["immirzi"],
            ),
        ),
        (
            "counterterm_radial_density_variation_inputs",
            lambda: write_density_variation_inputs(
                geometry_path=paths["geometry"],
                profile_path=paths["lct_profile"],
                output_path=paths["density_variation"],
            ),
        ),
        (
            "rsigma_E_counterterm",
            lambda: write_rsigma_counterterm(
                input_path=paths["density_variation"],
                output_path=paths["e_counterterm"],
            ),
        ),
    ]
    first_blocker = None
    for name, run in step_specs:
        payload = run()
        passed = _passed(payload)
        steps.append(
            {
                "name": name,
                "passed": passed,
                "blocker": None if passed else _blocker(payload),
                "next_required": [] if passed else payload.get("next_required", []),
                "required_input_fields": [] if passed else payload.get("required_input_fields", []),
                "payload_status": payload.get("status"),
            }
        )
        if not passed:
            first_blocker = steps[-1]["blocker"]
            break
    return {
        "status": "janus-z2-sigma-counterterm-chain",
        "active_core": "Z2_tunnel_Sigma",
        "chain_passed": first_blocker is None,
        "first_blocker": first_blocker or "none",
        "steps": steps,
        "independent_missing_inputs": [
            name
            for name, path in {
                "rsigma_radius_solution": paths["radius"],
                "surface_hk_active_density_coefficients": paths["surface_hk_coefficients"],
                "counterterm_trace_residual_inputs": paths["trace"],
            }.items()
            if not path.exists()
        ],
        "circular_dependency": {
            "detected": (not paths["radius"].exists()) and (not paths["e_counterterm"].exists()),
            "cycle": [
                "rsigma_radius_solution needs rsigma_E_counterterm",
                "rsigma_E_counterterm needs a radius grid for local density variation",
            ],
            "escape_condition": (
                "symbolic E_counterterm(R) closure is available; derive active "
                "surface_hk coefficients a0..a3 and solve the coupled radius equation, "
                "or derive R_Sigma from an independent global regularity equation"
            ),
        },
        "next_physical_equations": {
            "surface_density": "L_Sigma = a0 + a1 K + a2 K^2 + a3 K_ab K^ab",
            "active_coefficients_needed": ["a0(a)", "a1(a)", "a2(a)", "a3(a)"],
            "trace_route": [
                "derive alpha_h_radial and alpha_K_radial from full Sigma variation",
                "R_h_trace = alpha_h_radial/(2 R_Sigma sqrt|h|)",
                "R_K_trace = alpha_K_radial/sqrt|h|",
                "solve minimal coefficient system only after trace inputs exist",
            ],
            "direct_action_route": [
                "derive a0..a3 directly from the active Z2/Sigma surface action",
                "feed surface_hk_active_density_coefficients.json",
            ],
            "known_obstruction": (
                "minimal constant h/K basis alone underdetermines a0..a3; "
                "linear K duplicate is forbidden after Cartan-GHY partition"
            ),
        },
        "surface_hk_coefficient_route": {
            "gate": coefficient_route["status"],
            "passed": coefficient_route["gate_passed"],
            "selected_route": coefficient_route["selected_route"],
            "primary_blocker": coefficient_route["primary_blocker"],
            "next_required": coefficient_route["next_required"],
        },
        "trace_coefficient_cycle": {
            "detected": (
                not paths["trace"].exists()
                and not paths["surface_hk_coefficients"].exists()
                and not paths["alpha_radial"].exists()
            ),
            "cycle": [
                "counterterm_minimal_basis_coefficients needs counterterm_trace_residual_inputs",
                "counterterm_trace_residual_inputs needs alpha_res_radial_components",
                "alpha_res_radial_components needs surface_hk_active_density_coefficients",
                "surface_hk_active_density_coefficients needs minimal coefficients or a direct active Sigma action",
            ],
            "escape_condition": (
                "derive active R_h_trace/R_K_trace from the full Sigma variation, "
                "or derive a0..a3 directly from the active Z2/Sigma surface action"
            ),
        },
        "paths": {key: str(path) for key, path in paths.items()},
        "forbidden_shortcuts": [
            "no E_counterterm_zero assumption",
            "no fitted counterterm coefficient",
            "no linear-K duplicate after Cartan-GHY partition",
            "no archived Z4 inputs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Chain",
        "",
        f"Passed: `{payload['chain_passed']}`",
        f"First blocker: `{payload['first_blocker']}`",
        "",
        "## Steps",
    ]
    lines.extend(
        f"- `{step['name']}`: `{step['passed']}`"
        + ("" if step["passed"] else f" ({step['blocker']})")
        for step in payload["steps"]
    )
    failed = next((step for step in payload["steps"] if not step["passed"]), None)
    if failed:
        lines.extend(["", "## Failed Step Required Inputs"])
        lines.extend(f"- `{field}`" for field in failed.get("required_input_fields", []))
        lines.extend(["", "## Failed Step Next Required"])
        lines.extend(f"- `{item}`" for item in failed.get("next_required", []))
    lines.extend(["", "## Independent Missing Inputs"])
    lines.extend(f"- `{item}`" for item in payload["independent_missing_inputs"])
    if payload["circular_dependency"]["detected"]:
        lines.extend(["", "## Circular Dependency"])
        lines.extend(f"- `{item}`" for item in payload["circular_dependency"]["cycle"])
        lines.append(f"- escape: `{payload['circular_dependency']['escape_condition']}`")
    if payload["trace_coefficient_cycle"]["detected"]:
        lines.extend(["", "## Trace/Coefficient Cycle"])
        lines.extend(f"- `{item}`" for item in payload["trace_coefficient_cycle"]["cycle"])
        lines.append(f"- escape: `{payload['trace_coefficient_cycle']['escape_condition']}`")
    lines.extend(["", "## Next Physical Equations"])
    lines.append(f"- density: `{payload['next_physical_equations']['surface_density']}`")
    lines.append(
        "- coefficients: `"
        + ", ".join(payload["next_physical_equations"]["active_coefficients_needed"])
        + "`"
    )
    lines.append(f"- obstruction: `{payload['next_physical_equations']['known_obstruction']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
