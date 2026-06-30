from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_auxiliary_l_action_attempt import build_payload as build_aux_action
from scripts.build_p0_b4vol_jacobian_gauge_degeneracy_proof import (
    build_payload as build_b4vol_degeneracy,
)
from scripts.build_p0_integrability_first_phi_l_selection import (
    build_payload as build_integrability,
)
from scripts.build_p0_higher_derivative_dl_scouple_obstruction import (
    build_payload as build_higher_derivative,
)
from scripts.build_p0_curvature_scouple_selector_obstruction import (
    build_payload as build_curvature_scouple,
)
from scripts.build_p0_local_phi_scouple_no_go_target import build_payload as build_local_nogo
from scripts.build_p0_local_low_derivative_scouple_restricted_no_go import (
    build_payload as build_restricted_local_nogo,
)
from scripts.build_p0_lorentz_tetrad_selector_obstruction import (
    build_payload as build_lorentz,
)
from scripts.build_p0_matter_pullback_action_deep_audit import (
    build_payload as build_matter_pullback_deep,
)
from scripts.build_p0_noether_split_rank_obstruction import build_payload as build_noether
from scripts.build_p0_nonlocal_kernel_scouple_selector_obstruction import (
    build_payload as build_nonlocal_kernel,
)
from scripts.build_p0_phase_space_symplectic_selector_obstruction import (
    build_payload as build_phase_space,
)
from scripts.build_p0_pulled_particle_action_cuu_derivation import (
    build_payload as build_pulled_particle,
)


REPORT_PATH = Path("outputs/reports/p0_zero_rustine_phi_j_l_route_attack_matrix.md")
JSON_PATH = Path("outputs/reports/p0_zero_rustine_phi_j_l_route_attack_matrix.json")


def build_payload() -> dict:
    b4vol = build_b4vol_degeneracy()
    noether = build_noether()
    phase_space = build_phase_space()
    lorentz = build_lorentz()
    aux_action = build_aux_action()
    pulled_particle = build_pulled_particle()
    matter_pullback_deep = build_matter_pullback_deep()
    integrability = build_integrability()
    higher_derivative = build_higher_derivative()
    curvature_scouple = build_curvature_scouple()
    nonlocal_kernel = build_nonlocal_kernel()
    local_nogo = build_local_nogo()
    restricted_local_nogo = build_restricted_local_nogo()

    routes = [
        {
            "route": "b4vol_source_identity",
            "zero_rustine": True,
            "positive_result": "B4vol product identity and gauge degeneracy proved",
            "selects_phi_j_l": False,
            "next_required": "source-derived lapse/slice/gauge selector",
        },
        {
            "route": "noether_split",
            "zero_rustine": bool(noether["zero_rustine"]),
            "positive_result": "rank-one obstruction proved for single diagonal identity",
            "selects_phi_j_l": False,
            "next_required": "independent sector identity or source-derived split equation",
        },
        {
            "route": "phase_space_symplectic",
            "zero_rustine": True,
            "positive_result": "Liouville/canonical family preserves phase-space determinant",
            "selects_phi_j_l": bool(phase_space["phase_space_route_selects_j_phi"]),
            "next_required": "Hamiltonian/source branch selecting spacetime projection",
        },
        {
            "route": "lorentz_tetrad",
            "zero_rustine": True,
            "positive_result": "local Lorentz admissibility and det L=1 checked",
            "selects_phi_j_l": bool(lorentz["lorentz_admissibility_selects_jphi"]),
            "next_required": "source-derived rapidity/DL/same-L transport equation",
        },
        {
            "route": "pullback_particle_dust_action",
            "zero_rustine": True,
            "positive_result": "particle geodesic and cold-dust Cuu skeleton derived",
            "selects_phi_j_l": bool(pulled_particle["same_phi_l_source_selected"]),
            "next_required": "Janus-selected same phi/L in the pullback variation",
        },
        {
            "route": "matter_pullback_action_deep",
            "zero_rustine": True,
            "positive_result": "pure pullback EL identity and conditional dust force shape separated",
            "selects_phi_j_l": bool(matter_pullback_deep["same_phi_l_selection_derived"]),
            "next_required": "genuine Janus receiver/source coupled action, not passive pullback",
        },
        {
            "route": "auxiliary_l_scouple_action",
            "zero_rustine": not bool(aux_action["source_derived_action_found"]),
            "positive_result": "candidate can tie K_plus/K_minus/Q_cross to one L",
            "selects_phi_j_l": bool(aux_action["source_derived_action_found"]),
            "next_required": "source action or rejection as ansatz",
        },
        {
            "route": "integrability_first",
            "zero_rustine": bool(integrability["source_compatible"]),
            "positive_result": "source-compatible curl/Frobenius route written",
            "selects_phi_j_l": bool(integrability["uniqueness"]["forces_unique_phi_l"]),
            "next_required": "source equations plus boundary/initial data fixing a unique inverse map",
        },
        {
            "route": "higher_derivative_dl_scouple",
            "zero_rustine": True,
            "positive_result": "D L D L terms produce transport PDEs",
            "selects_phi_j_l": bool(higher_derivative["higher_derivative_terms_select_unique_phi_j_l"]),
            "next_required": "source-derived coefficient, boundary/source data, same-L proof, split Noether proof",
        },
        {
            "route": "curvature_scouple",
            "zero_rustine": True,
            "positive_result": "curvature couplings produce map equations",
            "selects_phi_j_l": bool(curvature_scouple["curvature_terms_select_unique_phi_j_l"]),
            "next_required": "source curvature branch, coefficients, boundary data, same-L residual proof",
        },
        {
            "route": "nonlocal_kernel_scouple",
            "zero_rustine": True,
            "positive_result": "nonlocal kernels can select a given target",
            "selects_phi_j_l": bool(
                nonlocal_kernel["nonlocal_route_selects_source_derived_phi_j_l"]
            ),
            "next_required": "source-derived kernel, target/current, causal boundary, mirror and same-L proof",
        },
        {
            "route": "restricted_low_derivative_scouple_no_go",
            "zero_rustine": True,
            "positive_result": "restricted easy local S_couple class eliminated",
            "selects_phi_j_l": False,
            "next_required": "extend proof to source-derived classes",
        },
        {
            "route": "local_low_derivative_no_go",
            "zero_rustine": True,
            "positive_result": "bounded theorem target stated",
            "selects_phi_j_l": False,
            "next_required": "prove or refute the bounded no-go theorem",
        },
    ]
    closed_routes = [row for row in routes if row["selects_phi_j_l"]]
    blockers = [
        "B4vol fixes only a product, not J_phi",
        "one diagonal Noether identity has rank 1, not two sector residual equations",
        "Liouville preservation fixes phase-space determinant, not spacetime J_phi",
        "Lorentz admissibility leaves rapidity and D L transport free",
        "particle/dust action skeleton still lacks Janus-selected same phi/L",
        "pure matter pullback is an identity; nonzero phi equation requires true S_couple",
        "integrability removes bad maps but does not prove uniqueness without source/boundary data",
        "higher-derivative D L terms give PDEs but still need source-derived coefficients and boundary data",
        "curvature couplings give equations but scalar matching is degenerate and needs source data",
        "nonlocal kernels can hard-code a selector unless kernel and target are source-derived",
        "restricted ultralocal S_couple families are eliminated but not every source action",
    ]
    return {
        "description": "Zero-rustine attack matrix for source-derived phi/J/L selection routes.",
        "status": "zero-rustine-routes-attacked-no-general-selector-yet",
        "routes": routes,
        "blockers": blockers,
        "routes_attacked": len(routes),
        "routes_selecting_phi_j_l": len(closed_routes),
        "any_route_selects_phi_j_l": bool(closed_routes),
        "b4vol_degeneracy_proved": bool(b4vol["degeneracy_symbolic_identity_closed"]),
        "noether_rank_obstruction_proved": bool(noether["diagonal_identity_rank"] == 1),
        "phase_space_obstruction_proved": bool(
            phase_space["canonical_liouville_det_equals_one"]
            and not phase_space["phase_space_route_selects_j_phi"]
        ),
        "lorentz_obstruction_proved": bool(
            lorentz["lorentz_condition_symbolically_closed"]
            and not lorentz["lorentz_admissibility_selects_jphi"]
        ),
        "pullback_dust_skeleton_available": bool(
            pulled_particle["particle_geodesic_variation_closed"]
            and pulled_particle["cold_dust_lift_closed"]
        ),
        "matter_pullback_deep_audit_completed": bool(
            matter_pullback_deep["deep_action_pullback_attempt_completed"]
        ),
        "pure_matter_pullback_selects_phi_j_l": bool(
            matter_pullback_deep["pure_matter_pullback_selects_phi_j_l"]
        ),
        "projected_dust_force_shape_derived": bool(
            matter_pullback_deep["projected_dust_force_shape_derived"]
        ),
        "auxiliary_scouple_remains_ansatz": bool(aux_action["new_axiom_risk"]),
        "integrability_first_source_compatible": bool(integrability["source_compatible"]),
        "higher_derivative_dl_route_produces_pde": bool(
            higher_derivative["higher_derivative_terms_produce_pde"]
        ),
        "higher_derivative_dl_route_selects_phi_j_l": bool(
            higher_derivative["higher_derivative_terms_select_unique_phi_j_l"]
        ),
        "curvature_scouple_route_produces_equations": bool(
            curvature_scouple["curvature_terms_produce_map_equations"]
        ),
        "curvature_scouple_route_selects_phi_j_l": bool(
            curvature_scouple["curvature_terms_select_unique_phi_j_l"]
        ),
        "nonlocal_kernel_can_select_given_target": bool(
            nonlocal_kernel["nonlocal_kernel_can_select_given_target"]
        ),
        "nonlocal_kernel_arbitrary_target_hiding_risk": bool(
            nonlocal_kernel["arbitrary_target_hiding_risk"]
        ),
        "nonlocal_kernel_route_selects_source_derived_phi_j_l": bool(
            nonlocal_kernel["nonlocal_route_selects_source_derived_phi_j_l"]
        ),
        "restricted_local_low_derivative_no_go_proved": bool(
            restricted_local_nogo["restricted_no_go_proved"]
        ),
        "local_no_go_theorem_proved": bool(local_nogo["theorem_proved"]),
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "hidden_axiom_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "recommended_next": [
            "derive independent split Noether/source identity, or prove it impossible",
            "derive Hamiltonian/source branch for phase-space projection to J_phi",
            "derive source rapidity/DL equation for same-L transport",
            "prove the local low-derivative no-go theorem to eliminate ansatz families",
        ],
        "verdict": (
            "All non-rustine routes tested here are useful but still non-selective for "
            "the general branch. The clean next work is not fitting: derive a new "
            "source identity/action equation, or prove a bounded no-go theorem."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Zero-Rustine Phi/J/L Route Attack Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Routes attacked: {payload['routes_attacked']}",
        f"Routes selecting phi/J/L: {payload['routes_selecting_phi_j_l']}",
        f"Any route selects phi/J/L: {payload['any_route_selects_phi_j_l']}",
        f"B4vol degeneracy proved: {payload['b4vol_degeneracy_proved']}",
        f"Noether rank obstruction proved: {payload['noether_rank_obstruction_proved']}",
        f"Phase-space obstruction proved: {payload['phase_space_obstruction_proved']}",
        f"Lorentz obstruction proved: {payload['lorentz_obstruction_proved']}",
        f"Pullback dust skeleton available: {payload['pullback_dust_skeleton_available']}",
        f"Matter pullback deep audit completed: {payload['matter_pullback_deep_audit_completed']}",
        f"Pure matter pullback selects phi/J/L: {payload['pure_matter_pullback_selects_phi_j_l']}",
        f"Projected dust force shape derived: {payload['projected_dust_force_shape_derived']}",
        f"Auxiliary S_couple remains ansatz: {payload['auxiliary_scouple_remains_ansatz']}",
        f"Integrability-first source compatible: {payload['integrability_first_source_compatible']}",
        f"Higher-derivative D L route produces PDE: {payload['higher_derivative_dl_route_produces_pde']}",
        (
            "Higher-derivative D L route selects phi/J/L: "
            f"{payload['higher_derivative_dl_route_selects_phi_j_l']}"
        ),
        f"Curvature S_couple route produces equations: {payload['curvature_scouple_route_produces_equations']}",
        f"Curvature S_couple route selects phi/J/L: {payload['curvature_scouple_route_selects_phi_j_l']}",
        f"Nonlocal kernel can select given target: {payload['nonlocal_kernel_can_select_given_target']}",
        (
            "Nonlocal kernel arbitrary target hiding risk: "
            f"{payload['nonlocal_kernel_arbitrary_target_hiding_risk']}"
        ),
        (
            "Nonlocal kernel route selects source-derived phi/J/L: "
            f"{payload['nonlocal_kernel_route_selects_source_derived_phi_j_l']}"
        ),
        (
            "Restricted local low-derivative no-go proved: "
            f"{payload['restricted_local_low_derivative_no_go_proved']}"
        ),
        f"Local no-go theorem proved: {payload['local_no_go_theorem_proved']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Hidden axiom used: {payload['hidden_axiom_used']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Routes",
        "",
        "| route | zero rustine | positive result | selects phi/J/L | next required |",
        "|---|---:|---|---:|---|",
    ]
    for row in payload["routes"]:
        lines.append(
            f"| {row['route']} | {row['zero_rustine']} | {row['positive_result']} | "
            f"{row['selects_phi_j_l']} | {row['next_required']} |"
        )
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Recommended Next", ""])
    lines.extend(f"- {item}" for item in payload["recommended_next"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
