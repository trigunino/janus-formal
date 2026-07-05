from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_action_readiness_gate import (
    build_payload as build_projected_dirac_action_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_torsion_pullback_on_sigma_gate import (
    build_payload as build_torsion_pullback_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_immirzi_bulk_boundary_equation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_immirzi_bulk_boundary_equation_gate.json")


def build_payload(
    *,
    torsion_pullback_payload: dict | None = None,
    projected_dirac_payload: dict | None = None,
) -> dict:
    torsion = torsion_pullback_payload or build_torsion_pullback_payload()
    projected_dirac = projected_dirac_payload or build_projected_dirac_action_readiness_payload()
    torsion_ready = bool(torsion["closure"]["torsion_pullback_on_Sigma_ready"])
    spinor_source_ready = bool(
        projected_dirac["readiness"]["Z2_projected_Dirac_action_ready"]
        and projected_dirac["readiness"]["Holst_fermion_coupling_formula_ready"]
    )
    declared = {
        "variation_bibliography_checked": True,
        "scalar_Immirzi_Holst_variation_imported": True,
        "Nieh_Yan_variation_imported": True,
        "bulk_Euler_Lagrange_slot_declared": True,
        "Sigma_boundary_term_declared": True,
        "torsion_pullback_required": True,
        "torsion_pullback_on_Sigma_gate_declared": True,
        "spinor_source_required": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "bulk_Immirzi_equation_reduced": torsion_ready and spinor_source_ready,
        "Sigma_boundary_condition_reduced": torsion_ready and spinor_source_ready,
        "torsion_pullback_ready": torsion_ready,
        "spinor_source_ready": spinor_source_ready,
        "Immirzi_bulk_boundary_equation_ready": torsion_ready and spinor_source_ready,
    }
    return {
        "status": "janus-z2-sigma-immirzi-bulk-boundary-equation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Taveras and Yunes 2008 scalar Immirzi Holst variation",
            "Mercuri 2009 Nieh-Yan/Immirzi field coupling",
            "projective invariant Nieh-Yan field-equation literature",
            "active torsion-pullback-on-Sigma gate",
        ],
        "bibliography_result": (
            "Generic scalar-Immirzi Holst/Nieh-Yan variation provides the form of "
            "a bulk Euler-Lagrange equation plus boundary terms. The active Janus "
            "Z2/Sigma reduction still requires the Sigma torsion pullback and spinor source."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "torsion_pullback_on_Sigma": {
                "gate": torsion["status"],
                "ready": torsion["torsion_pullback_on_sigma_ready"],
                "current_frontier": torsion["current_frontier"],
            },
            "projected_Dirac_action_readiness": {
                "gate": projected_dirac["status"],
                "ready": projected_dirac["projected_dirac_action_readiness_ready"],
                "still_open": projected_dirac["still_open"],
            },
        },
        "formulas": {
            "bulk_slot": "E_gamma = delta S_HolstNiehYan / delta gamma_Immirzi = 0",
            "sigma_boundary_slot": "B_gamma^Sigma = boundary_term(delta_gamma S_Sigma) = 0",
            "source_dependency": "E_gamma,B_gamma depend on NY_pullback(T,e,omega) and spinor/torsion sources",
        },
        "immirzi_bulk_boundary_ledger_declared": all(declared.values()),
        "immirzi_bulk_boundary_equation_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "torsion_pullback_on_Sigma"
            if not torsion_ready
            else "projected_Dirac_action_readiness"
        ),
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "derive_Z2Sigma_torsion_pullback",
            "pass_torsion_pullback_on_Sigma_gate",
            "derive_active_spinor_source_for_Immirzi_variation",
            "reduce_bulk_Immirzi_Euler_Lagrange_equation",
            "reduce_Sigma_Immirzi_boundary_condition",
            "feed_equations_to_Immirzi_profile_of_a_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Immirzi Bulk/Boundary Equation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['immirzi_bulk_boundary_ledger_declared']}`",
        f"Equation ready: `{payload['immirzi_bulk_boundary_equation_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
