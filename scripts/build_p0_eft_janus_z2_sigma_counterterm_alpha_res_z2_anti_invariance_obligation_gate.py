from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_sigma_boundary_nonlinear_residual_closure_gate import (
    build_payload as build_nonlinear_closure,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_z2_odd_residual_projection_route_gate import (
    build_payload as build_z2_odd_route,
)
from scripts.build_p0_eft_janus_z2_sigma_dirac_current_parity_from_spinor_intertwiner_gate import (
    build_payload as build_dirac_current_parity,
)
from scripts.build_p0_eft_janus_z2_sigma_equivariant_flux_cancellation_gate import (
    build_payload as build_flux_cancellation,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_torsion_flux_zero_or_equivariance_gate import (
    build_payload as build_holst_flux,
)
from scripts.build_p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate import (
    build_payload as build_orientation,
)
from scripts.build_p0_eft_janus_z2_sigma_stress_equivariance_gate import (
    build_payload as build_stress_equivariance,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_alpha_res_z2_anti_invariance_obligation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_alpha_res_z2_anti_invariance_obligation_gate.json"
)


def build_payload() -> dict:
    orientation = build_orientation()
    nonlinear = build_nonlinear_closure()
    route = build_z2_odd_route()
    stress = build_stress_equivariance()
    flux = build_flux_cancellation()
    holst = build_holst_flux()
    current = build_dirac_current_parity()

    component_emission = nonlinear["component_emission"]
    alpha_components_available = component_emission["alpha_res_components_available"]
    alpha_component_decomposition_available = component_emission.get(
        "alpha_res_component_decomposition_available", alpha_components_available
    )
    alpha_component_values_available = component_emission.get(
        "alpha_res_component_values_available", False
    )
    alpha_component_names = component_emission.get("alpha_res_component_names", [])

    channel_tests = {
        "orientation_normal_channel": {
            "ready": orientation["projective_gluing_normal_orientation_sign_ready"],
            "required_parity": "odd",
            "formula": "n_- = - tau_Z2_* n_+",
        },
        "matter_flux_channel": {
            "ready": flux["z2_flux_cancellation_derived"],
            "required_parity": "odd_or_cancelled",
            "formula": "F_a^+ + eps_Z2 F_a^- = 0",
        },
        "holst_torsion_channel": {
            "ready": holst["holst_torsion_flux_zero_or_equivariance_ready"],
            "required_parity": "zero_or_equivariant",
            "formula": "E_HolstNiehYan = 0 or T_Holst^- = tau_* T_Holst^+",
        },
        "stress_tensor_channel": {
            "ready": stress["stress_equivariance_ready"],
            "required_parity": "equivariant",
            "formula": "T_total^- = tau_* T_total^+",
        },
        "spinor_current_channel": {
            "ready": current["dirac_current_z2_parity_ready"],
            "required_parity": "equivariant_or_cancelled",
            "formula": "J_- = tau_Z2_* J_+",
        },
        "residual_component_channel": {
            "ready": alpha_component_decomposition_available,
            "required_parity": "componentwise_odd",
            "formula": "tau_Z2^* alpha_res_i = - alpha_res_i for every emitted component",
        },
    }
    component_parity_tests = {
        "metric_tetrad_component": {
            "component_declared": "metric_tetrad_component" in alpha_component_names,
            "parity_proved": False,
            "blocker": "R_h_ab_value_and_Z2_pullback_parity",
        },
        "extrinsic_tetrad_component": {
            "component_declared": "extrinsic_tetrad_component" in alpha_component_names,
            "parity_proved": False,
            "blocker": "R_K_ab_value_and_Z2_normal_orientation_parity",
        },
        "torsion_pullback_component": {
            "component_declared": "torsion_pullback_component" in alpha_component_names,
            "parity_proved": holst["holst_torsion_flux_zero_or_equivariance_ready"],
            "blocker": "none"
            if holst["holst_torsion_flux_zero_or_equivariance_ready"]
            else "torsion_pullback_Z2_parity",
        },
        "immirzi_radion_component": {
            "component_declared": "immirzi_radion_component" in alpha_component_names,
            "parity_proved": False,
            "blocker": "full_R_chi_component_Z2_parity",
        },
        "connection_component": {
            "component_declared": "connection_component" in alpha_component_names,
            "parity_proved": False,
            "blocker": "connection_pullback_Z2_parity",
        },
        "spinor_component": {
            "component_declared": "spinor_component" in alpha_component_names,
            "parity_proved": current["dirac_current_z2_parity_ready"],
            "blocker": "none"
            if current["dirac_current_z2_parity_ready"]
            else current["primary_blocker"],
        },
        "embedding_component": {
            "component_declared": "embedding_component" in alpha_component_names,
            "parity_proved": flux["closure"].get("Z2_equivariant_embedding_derived", False),
            "blocker": "none"
            if flux["closure"].get("Z2_equivariant_embedding_derived", False)
            else "Z2_equivariant_embedding_derived",
        },
        "matter_flux_component": {
            "component_declared": "matter_flux_component" in alpha_component_names,
            "parity_proved": flux["z2_flux_cancellation_derived"],
            "blocker": "none" if flux["z2_flux_cancellation_derived"] else flux["primary_blocker"],
        },
    }
    all_components_declared = bool(component_parity_tests) and all(
        item["component_declared"] for item in component_parity_tests.values()
    )
    all_emitted_components_odd = all_components_declared and all(
        item["parity_proved"] for item in component_parity_tests.values()
    )
    channel_closure_ready = all(item["ready"] for item in channel_tests.values())
    anti_invariance_ready = (
        route["declared"]["Z2_orientation_reversal_available"]
        and alpha_component_decomposition_available
        and channel_closure_ready
        and all_emitted_components_odd
    )
    quotient_cancellation_ready = (
        anti_invariance_ready and route["closure"]["paired_sheet_residual_support_proved"]
    )
    counterterm_zero_ready = quotient_cancellation_ready

    blockers = [key for key, item in channel_tests.items() if not item["ready"]]
    if not route["closure"]["paired_sheet_residual_support_proved"]:
        blockers.append("paired_sheet_residual_support")
    priority_blockers = []
    if not alpha_component_decomposition_available:
        priority_blockers.append("residual_component_channel")
    if alpha_component_decomposition_available and not all_emitted_components_odd:
        priority_blockers.append("componentwise_parity_proofs")
    priority_blockers.extend(key for key in blockers if key not in priority_blockers)

    return {
        "status": "janus-z2-sigma-counterterm-alpha-res-z2-anti-invariance-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "route": "Z2_odd_residual_projection",
        "declared": {
            "anti_invariance_obligation_declared": True,
            "componentwise_channel_test_declared": True,
            "quotient_cancellation_consequence_declared": True,
            "density_ansatz_forbidden": True,
            "fitted_counterterm_coefficient_forbidden": True,
            "legacy_z4_reuse_forbidden": True,
        },
        "formulae": {
            "target": "tau_Z2^* alpha_res = - alpha_res",
            "component_test": "alpha_res = sum_i alpha_i and tau_Z2^* alpha_i = - alpha_i",
            "quotient_cancellation": "pi_* alpha_res = 0 on Sigma/Z2",
            "counterterm_consequence": "E_counterterm = 0 without constructing L_ct",
        },
        "channel_tests": channel_tests,
        "component_parity_tests": component_parity_tests,
        "closure": {
            "alpha_res_components_available": alpha_components_available,
            "alpha_res_component_decomposition_available": alpha_component_decomposition_available,
            "alpha_res_component_values_available": alpha_component_values_available,
            "all_components_declared": all_components_declared,
            "all_emitted_components_odd": all_emitted_components_odd,
            "componentwise_channel_closure_ready": channel_closure_ready,
            "alpha_res_Z2_anti_invariance_proved": anti_invariance_ready,
            "paired_sheet_residual_support_proved": route["closure"][
                "paired_sheet_residual_support_proved"
            ],
            "quotient_projection_cancels_alpha_res": quotient_cancellation_ready,
            "E_counterterm_zero_without_density": counterterm_zero_ready,
        },
        "upstream_frontiers": {
            "nonlinear_residual_closure": {
                "gate": nonlinear["status"],
                "closed": nonlinear["sigma_nonlinear_boundary_residual_closed"],
                "component_emission": component_emission,
            },
            "stress_equivariance": {
                "gate": stress["status"],
                "ready": stress["stress_equivariance_ready"],
                "primary_blocker": stress["primary_blocker"],
                "closure": stress["closure"],
            },
            "flux_cancellation": {
                "gate": flux["status"],
                "ready": flux["z2_flux_cancellation_derived"],
                "primary_blocker": flux["primary_blocker"],
            },
            "dirac_current_parity": {
                "gate": current["status"],
                "ready": current["dirac_current_z2_parity_ready"],
                "primary_blocker": current["primary_blocker"],
                "route_blockers": current.get("equivariance_route_blockers", []),
            },
            "holst_flux": {
                "gate": holst["status"],
                "ready": holst["holst_torsion_flux_zero_or_equivariance_ready"],
                "primary_blocker": holst["primary_blocker"],
            },
        },
        "route_status": "credible_but_blocked"
        if not counterterm_zero_ready
        else "closed",
        "gate_passed": counterterm_zero_ready,
        "primary_blocker": "none" if counterterm_zero_ready else priority_blockers[0],
        "blockers": blockers,
        "interpretation": (
            "The Janus/Z2 bypass is not dead: normal orientation reversal and the "
            "Holst torsionless boundary slot are available. It is not closed either: "
                "the nonlinear Sigma gate now emits a component schema, but matter/stress/spinor "
                "equivariance and tetrad/connection component parities are not yet strong enough to prove componentwise oddness of "
                "alpha_res."
        ),
        "next_required": []
        if counterterm_zero_ready
        else [
            "prove_componentwise_tau_Z2_pullback_alpha_i_equals_minus_alpha_i",
            "emit_explicit_alpha_res_component_values_for_tetrad_connection_chi_channels",
            "close_total_stress_Z2_equivariance_or_prove_flux_slot_zero",
            "close_Dirac_current_Z2_parity_or prove_spinor_residual_pairing_zero",
            "prove_paired_sheet_residual_support_on_Sigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Alpha_res Z2 Anti-Invariance Obligation Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Channel Tests",
    ]
    for name, item in payload["channel_tests"].items():
        lines.append(
            f"- `{name}`: ready=`{item['ready']}`, required=`{item['required_parity']}`"
        )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
