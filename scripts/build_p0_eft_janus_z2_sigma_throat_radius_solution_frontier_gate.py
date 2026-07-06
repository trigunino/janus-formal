from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_reduction_frontier_gate import (
    build_payload as build_counterterm_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_system_gate import (
    build_payload as build_coupled_radius_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_frontier_gate import (
    build_payload as build_matter_flux_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_radius_to_embedding_conditional_closure_gate import (
    build_payload as build_radius_to_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_throat_radius_variational_equation_gate import (
    build_payload as build_variational_equation_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_sqrt_intrinsic_curvature_counterterm_gate import (
    build_payload as build_sqrt_intrinsic_counterterm_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate.json")


def build_payload() -> dict:
    coupled_flux = build_coupled_radius_flux_payload()
    matter_flux_frontier = build_matter_flux_frontier_payload()
    counterterm = build_counterterm_frontier_payload()
    sqrt_intrinsic_counterterm = build_sqrt_intrinsic_counterterm_payload()
    variational = build_variational_equation_payload()
    radius_to_embedding = build_radius_to_embedding_payload()
    declared = {
        "variational_equation_gate_imported": True,
        "block_dependency_audit_imported": True,
        "matter_flux_radial_block_imported": True,
        "matter_flux_frontier_gate_imported": True,
        "coupled_radius_flux_system_gate_imported": True,
        "counterterm_radial_block_imported": True,
        "radius_to_embedding_conditional_closure_imported": True,
        "thin_shell_radius_bibliography_checked": True,
        "no_fit_solution_certificate_declared": True,
    }
    status = {
        "variational_equation_ready": variational[
            "throat_radius_variational_equation_ready"
        ],
        "conditional_embedding_map_ready": radius_to_embedding[
            "radius_to_embedding_conditional_ready"
        ],
        "matter_flux_transparency_or_projection_frontier_ready": matter_flux_frontier[
            "matter_flux_frontier_ready"
        ],
        "coupled_radius_flux_solution_ready": coupled_flux[
            "coupled_radius_flux_solution_ready"
        ],
        "matter_flux_block_reduced": matter_flux_frontier["matter_flux_frontier_ready"]
        or coupled_flux["coupled_radius_flux_solution_ready"],
        "counterterm_block_reduced": counterterm["counterterm_radial_reduction_ready"],
        "sqrt_intrinsic_counterterm_cancels_cartan": sqrt_intrinsic_counterterm[
            "closure_result"
        ]["counterterm_cancels_CartanGHY_for_any_positive_R"],
        "sqrt_intrinsic_counterterm_fixes_radius": sqrt_intrinsic_counterterm[
            "closure_result"
        ]["R_Sigma_of_a_fixed"],
        "all_radial_blocks_reduced": False,
        "R_Sigma_equation_solved": variational["equation"]["R_Sigma_equation_solved"],
        "R_Sigma_of_a_ready": variational["equation"]["R_Sigma_of_a_ready"],
        "X_plus_minus_unconditional_ready": radius_to_embedding["closure"][
            "X_plus_minus_of_a_ready"
        ],
    }
    status["all_radial_blocks_reduced"] = (
        status["matter_flux_block_reduced"] and status["counterterm_block_reduced"]
    )
    current_frontier = []
    nearest_unresolved_radial_block = None
    if not status["matter_flux_block_reduced"]:
        current_frontier.append(
            "matter_flux_block_reduced = false via MatterFluxFrontierGate or CoupledRadiusFluxSystemGate"
        )
        nearest_unresolved_radial_block = {
            "block": "matter_flux",
            "gate": "P0EFTJanusZ2SigmaMatterFluxFrontierGate",
            "primary_blocker": matter_flux_frontier["primary_blocker"],
            "required": [
                "derive active Sigma transparency",
                "or derive explicit active normal flux projection F_a^Z2Sigma(a)",
                "then reduce E_matterFlux radial block",
            ],
            "diagnostic_only": True,
        }
    if not status["counterterm_block_reduced"]:
        current_frontier.append(
            "counterterm_block_reduced = false via CountertermRadialReductionFrontierGate"
        )
        if nearest_unresolved_radial_block is None:
            nearest_unresolved_radial_block = {
                "block": "counterterm",
                "gate": "P0EFTJanusZ2SigmaCountertermRadialReductionFrontierGate",
                "primary_blocker": counterterm["primary_blocker"],
                "required": [
                    "extract residual one-form coefficients",
                    "prove integrability and integrate primitive",
                    "expand local density and reduce E_counterterm radial block",
                ],
                "diagnostic_only": True,
            }
    if status["all_radial_blocks_reduced"] and not status["R_Sigma_equation_solved"]:
        current_frontier.append("R_Sigma_equation_solved = false")
        nearest_unresolved_radial_block = {
            "block": "R_Sigma_equation",
            "gate": "P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate",
            "primary_blocker": variational["primary_blocker"],
            "required": [
                "expand full E_RSigma(a)",
                "solve E_RSigma(a)=0 without observational fit",
            ],
            "diagnostic_only": True,
        }
    nearest_radial_block_frontier = {
        "cartan_ghy": "structurally reduced; waits for R_Sigma(a) and X_plus_minus(a)",
        "matter_flux": {
            "primary_blocker": matter_flux_frontier["primary_blocker"],
            "frontier_route": matter_flux_frontier["current_frontier"],
            "coupled_route": coupled_flux["current_frontier"],
        },
        "counterterm": {
            "primary_blocker": counterterm["primary_blocker"],
            "current_frontier": counterterm["current_frontier"],
        },
        "priority_rule": (
            "reduce matter-flux and counterterm before solving E_RSigma(a)=0; "
            "do not fit R_Sigma(a) or DeltaK_s/tau(a)"
        ),
    }
    return {
        "status": "janus-z2-sigma-throat-radius-solution-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Darmois-Israel shell radius variational equation methods",
            "Poisson-Visser thin-shell throat radius dynamics",
            "active Janus/Sigma radial block dependency audit",
        ],
        "bibliography_result": (
            "Standard thin-shell references justify solving a throat-radius equation "
            "once all source blocks are explicit. They do not provide the active "
            "Janus/Sigma solution certificate."
        ),
        "declared": declared,
        "status_flags": status,
        "upstream_frontiers": {
            "variational_equation": {
                "gate": variational["status"],
                "ready": variational["throat_radius_variational_equation_ready"],
                "closure_ready": variational["throat_radius_variational_closure_ready"],
                "equation": variational["equation"],
                "next_required": variational["next_required"],
            },
            "radius_to_embedding": {
                "gate": radius_to_embedding["status"],
                "conditional_ready": radius_to_embedding[
                    "radius_to_embedding_conditional_ready"
                ],
                "unconditional_ready": radius_to_embedding[
                    "radius_to_embedding_unconditional_ready"
                ],
                "closure": radius_to_embedding["closure"],
                "next_required": radius_to_embedding["next_required"],
            },
            "matter_flux_frontier": {
                "gate": matter_flux_frontier["status"],
                "frontier_ready": matter_flux_frontier["matter_flux_frontier_ready"],
                "transparency_path_ready": matter_flux_frontier[
                    "matter_flux_transparency_path_ready"
                ],
                "active_projection_path_ready": matter_flux_frontier[
                    "matter_flux_active_projection_path_ready"
                ],
                "primary_blocker": matter_flux_frontier["primary_blocker"],
                "current_frontier": matter_flux_frontier["current_frontier"],
            },
            "coupled_radius_flux": {
                "gate": coupled_flux["status"],
                "system_ready": coupled_flux["coupled_radius_flux_system_ready"],
                "solution_ready": coupled_flux["coupled_radius_flux_solution_ready"],
                "current_frontier": coupled_flux["current_frontier"],
            },
            "counterterm": {
                "gate": counterterm["status"],
                "reduction_ready": counterterm["counterterm_radial_reduction_ready"],
                "primary_blocker": counterterm["primary_blocker"],
                "current_frontier": counterterm["current_frontier"],
            },
            "sqrt_intrinsic_counterterm": {
                "gate": sqrt_intrinsic_counterterm["status"],
                "cancels_CartanGHY_for_any_positive_R": sqrt_intrinsic_counterterm[
                    "closure_result"
                ]["counterterm_cancels_CartanGHY_for_any_positive_R"],
                "R_Sigma_of_a_fixed": sqrt_intrinsic_counterterm["closure_result"][
                    "R_Sigma_of_a_fixed"
                ],
                "primary_blocker": sqrt_intrinsic_counterterm["primary_blocker"],
                "next_required": sqrt_intrinsic_counterterm["next_required"],
            },
        },
        "solution_certificate_rule": (
            "E_RSigma(a)=0 can yield R_Sigma(a) only after matter-flux and "
            "counterterm radial blocks are reduced and the radial equation is not a "
            "flat direction; no observational radius fit is allowed."
        ),
        "new_counterterm_diagnostic": (
            "The sqrt(R[h]) intrinsic counterterm cancels the round Cartan-GHY radial "
            "block for any positive R_Sigma, but it leaves R_Sigma(a) unfixed."
        ),
        "current_frontier": current_frontier,
        "nearest_unresolved_radial_block": nearest_unresolved_radial_block,
        "nearest_primary_blocker": (
            nearest_unresolved_radial_block.get("primary_blocker")
            if nearest_unresolved_radial_block is not None
            else "none"
        ),
        "nearest_unresolved_radial_block_declared": nearest_unresolved_radial_block is not None,
        "nearest_unresolved_radial_block_diagnostic_only": (
            nearest_unresolved_radial_block is not None
            and nearest_unresolved_radial_block["diagnostic_only"]
        ),
        "nearest_radial_block_frontier": nearest_radial_block_frontier,
        "downstream_unblocked_when_solved": [
            "instantiate_radius_to_embedding_conditional_closure_with_R_Sigma_of_a",
            "derive_X_plus_minus_of_a",
            "feed_X_plus_minus_to_tangent_normal_and_pullback_gates",
        ],
        "throat_radius_solution_frontier_ledger_declared": all(declared.values()),
        "throat_radius_solution_certificate_ready": all(declared.values())
        and status["variational_equation_ready"]
        and status["matter_flux_block_reduced"]
        and status["counterterm_block_reduced"]
        and status["all_radial_blocks_reduced"]
        and status["R_Sigma_equation_solved"]
        and status["R_Sigma_of_a_ready"],
        "embedding_unblocked_by_radius_solution": all(declared.values())
        and all(status.values()),
        "primary_blocker": (
            "none"
            if (
                all(declared.values())
                and status["variational_equation_ready"]
                and status["matter_flux_block_reduced"]
                and status["counterterm_block_reduced"]
                and status["all_radial_blocks_reduced"]
                and status["R_Sigma_equation_solved"]
                and status["R_Sigma_of_a_ready"]
            )
            else (
                f"{nearest_unresolved_radial_block['block']}_radial_block"
                if nearest_unresolved_radial_block is not None
                else "R_Sigma_variational_solution"
            )
        ),
        "next_required": [
            "close_matter_flux_radial_block_or_derive_transparency",
            "close_counterterm_residual_extraction_and_density_expansion",
            "reduce_counterterm_radial_block",
            "if_using_sqrt_Rh_counterterm_derive_extra_boundary_condition_for_RSigma_modulus",
            "expand_full_E_RSigma",
            "solve_E_RSigma_equals_zero_without_fit",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Throat Radius Solution Frontier Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['throat_radius_solution_frontier_ledger_declared']}`",
        f"Solution certificate ready: `{payload['throat_radius_solution_certificate_ready']}`",
        f"Embedding unblocked: `{payload['embedding_unblocked_by_radius_solution']}`",
        "",
        "## Rule",
        payload["solution_certificate_rule"],
        "",
        "## Current Frontier",
    ]
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Nearest Radial Block Frontier"])
    nearest = payload["nearest_unresolved_radial_block"]
    if nearest is not None:
        lines.append(f"- `nearest_unresolved_radial_block`: `{nearest['block']}`")
        lines.append(f"- `nearest_gate`: `{nearest['gate']}`")
        lines.extend(f"- `nearest_required`: `{item}`" for item in nearest["required"])
    lines.append(f"- `cartan_ghy`: {payload['nearest_radial_block_frontier']['cartan_ghy']}")
    matter_flux_frontier = payload["nearest_radial_block_frontier"]["matter_flux"]
    lines.extend(
        f"- `matter_flux/frontier_route`: `{item}`"
        for item in matter_flux_frontier["frontier_route"]
    )
    lines.extend(
        f"- `matter_flux/coupled_route`: `{item}`"
        for item in matter_flux_frontier["coupled_route"]
    )
    lines.extend(
        f"- `counterterm`: `{item}`"
        for item in payload["nearest_radial_block_frontier"]["counterterm"]
    )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
