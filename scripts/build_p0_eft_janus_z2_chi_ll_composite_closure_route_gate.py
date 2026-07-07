from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_area_gap_exit_gate import build_payload as area_gap
from scripts.build_p0_eft_janus_z2_sigma_area_spectrum_closure_gate import (
    build_payload as area_spectrum,
)
from scripts.build_p0_eft_janus_z2_sigma_area_flux_dual_closure_gate import (
    build_payload as area_flux_dual,
)
from scripts.build_p0_eft_janus_z2_sigma_no_rustine_area_flux_lock_closure import (
    build_payload as no_rustine_lock,
)
from scripts.build_p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate import (
    build_payload as flux_area_puncture,
)
from scripts.build_p0_eft_janus_z2_sigma_chern_su2_puncture_bridge_gate import (
    build_payload as chern_su2_puncture_bridge,
)
from scripts.build_p0_eft_janus_z2_sigma_route_b_max_closure_gate import (
    build_payload as route_b,
)
from scripts.build_p0_eft_janus_z2_chi_ll_area_flux_compatibility_gate import (
    build_payload as area_flux,
)
from scripts.build_p0_eft_janus_z2_chi_ll_area_flux_micro_parameter_constraint import (
    build_payload as area_flux_micro,
)
from scripts.build_p0_eft_janus_z2_chi_ll_route_a_lambda_over_q_origin_gate import (
    build_payload as route_a,
)
from scripts.build_p0_eft_janus_z2_chi_ll_single_micro_normalization_frontier_gate import (
    build_payload as single_micro,
)
from scripts.build_p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate import (
    build_payload as casimir,
)
from scripts.build_p0_eft_janus_z2_chi_ll_eight_exit_coverage_audit import (
    build_payload as coverage,
)
from scripts.build_p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate import (
    build_payload as horizon,
)
from scripts.build_p0_eft_janus_z2_chi_ll_spectral_bridge_matrix import (
    build_payload as spectral_bridge,
)
from scripts.build_p0_eft_janus_z2_chi_ll_spectral_stability_exit_gate import (
    build_payload as spectral,
)
from scripts.build_p0_eft_janus_z2_chi_ll_uv_ll_action_exit_gate import (
    build_payload as uv_ll,
)
from scripts.build_p0_eft_janus_z2_chi_ll_will_action_power_selection_gate import (
    build_payload as will_power,
)
from scripts.build_p0_eft_janus_z2_chi_ll_will_flux_radius_reducer_gate import (
    build_payload as will_radius,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_composite_closure_route_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_composite_closure_route_gate.json")


def build_payload() -> dict:
    area = area_gap()
    spectrum_area = area_spectrum()
    dual = area_flux_dual()
    no_rustine = no_rustine_lock()
    puncture = flux_area_puncture()
    chern_bridge = chern_su2_puncture_bridge()
    route_b_max = route_b()
    af = area_flux()
    afm = area_flux_micro()
    route_a_ratio = route_a()
    sm = single_micro()
    spec = spectral()
    cas = casimir()
    hor = horizon()
    ll = uv_ll()
    will = will_power()
    wr = will_radius()
    cov = coverage()
    spectral_report = spectral_bridge()
    chain = {
        "geometry_area_selector": {
            "route": "sigma_area_spectrum_closure -> area_gap_exit plus area_flux_compatibility/micro-parameter constraint, or regularity_global_closure_exit + absolute collar scale",
            "ready": route_b_max["chi_LL_prediction_ready"]
            and dual["area_flux_dual_closure_ready"]
            and spectrum_area["R_s_prediction_ready"]
            and area["area_gap_exit_ready"]
            and af["area_flux_compatibility_ready"]
            and afm["both_micro_parameters_consistent"]
            and sm["both_micro_inputs_consistent"],
            "provides": ["R_s", "A_Sigma"],
            "blocker": "no Sigma area operator / Holst area spectrum inputs / N_gap state selection / matching S2 flux radius / invariant lambda_F2/q_LL",
        },
        "mode_spectrum": {
            "route": "spectral_stability_exit",
            "ready": spec["spectral_stability_exit_ready"],
            "provides": ["1/R_s mode scale", "Dirac/Laplacian spectrum"],
            "blocker": "no active self-adjoint operator plus scale-selection law",
        },
        "source_generation": {
            "route": "Casimir_topological_exit or spin_condensate_exit",
            "ready": cas["casimir_exit_prediction_ready"],
            "provides": ["rho_Casimir or spin/torsion source"],
            "blocker": "no field content/boundary conditions/C or spin occupation",
        },
        "horizon_energy_check": {
            "route": "horizon_thermodynamic_exit",
            "ready": hor["horizon_thermodynamic_exit_ready"],
            "provides": ["horizon energy", "temperature/entropy consistency"],
            "blocker": "no proved horizon status / kappa_l / first law energy",
        },
        "ll_tension_map": {
            "route": "UV_LL_action_exit",
            "ready": ll["UV_LL_action_exit_ready"] or route_a_ratio["route_a_origin_ready"],
            "provides": ["chi_LL from LL action normalization"],
            "blocker": "WILL fixes p=1/2 and R_s(lambda_F2/q_LL,n), but no active invariant ratio lambda_F2/q_LL",
        },
        "global_charge_interpretation": {
            "route": "state_charge_exit",
            "ready": False,
            "provides": ["superselection sector label"],
            "blocker": "no active mass Casimir / Noether state",
        },
    }
    ready = all(step["ready"] for step in chain.values())
    return {
        "status": "janus-z2-chi-ll-composite-closure-route-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "coverage_status": cov["status"],
        "sigma_area_spectrum_status": spectrum_area["status"],
        "area_flux_dual_status": dual["status"],
        "no_rustine_area_flux_lock_status": no_rustine["status"],
        "flux_area_puncture_theorem_status": puncture["status"],
        "flux_area_puncture_theorem_ready": puncture["puncture_theorem_ready"],
        "chern_su2_puncture_bridge_status": chern_bridge["status"],
        "chern_su2_puncture_bridge_ready": chern_bridge["chern_to_su2_puncture_bridge_ready"],
        "N_gap_equals_abs_n_ready": chern_bridge["N_gap_equals_abs_n_ready"],
        "route_b_max_status": route_b_max["status"],
        "spectral_bridge_status": spectral_report["status"],
        "area_flux_compatibility_status": af["status"],
        "area_flux_micro_parameter_status": afm["status"],
        "route_a_lambda_over_q_status": route_a_ratio["status"],
        "single_micro_normalization_status": sm["status"],
        "will_action_power_selection_status": will["status"],
        "will_flux_radius_reducer_status": wr["status"],
        "physical_statement": (
            "The eight exits are mutually compatible as a composite closure chain. "
            "The chain would close chi_LL if one selector fixed R_s/A_Sigma and "
            "the downstream spectral/source/horizon/LL-action maps were active. "
            "In the current workspace every step is still conditional."
        ),
        "chain": chain,
        "first_blocker": next((name for name, step in chain.items() if not step["ready"]), None),
        "composite_route_ready": ready,
        "chi_LL_prediction_ready": ready,
        "best_next_physical_target": "geometry_area_selector",
        "why": (
            "Area/R_s selection is upstream of the spectral, Casimir, horizon and "
            "LL-action maps. Without it, all downstream relations remain functions "
            "of R_s rather than predictions."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Composite Closure Route Gate",
        "",
        payload["physical_statement"],
        "",
        f"Composite route ready: `{payload['composite_route_ready']}`",
        f"First blocker: `{payload['first_blocker']}`",
        f"Best next physical target: `{payload['best_next_physical_target']}`",
        "",
        "## Chain",
    ]
    for name, step in payload["chain"].items():
        lines.append(f"- `{name}`: ready=`{step['ready']}`; blocker={step['blocker']}")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
