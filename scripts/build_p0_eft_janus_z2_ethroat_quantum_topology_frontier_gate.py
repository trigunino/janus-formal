from __future__ import annotations

import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_area_gap_exit_gate import build_payload as area_gap
from scripts.build_p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate import (
    build_payload as casimir,
)
from scripts.build_p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate import (
    build_payload as horizon,
)
from scripts.build_p0_eft_janus_z2_chi_ll_regularity_global_closure_exit_gate import (
    build_payload as regularity,
)
from scripts.build_p0_eft_janus_z2_chi_ll_uv_ll_action_exit_gate import (
    build_payload as uv_ll,
)
from scripts.build_p0_eft_janus_z2_global_action_onshell_alpha_selector_gate import (
    build_payload as global_action,
)
from scripts.build_p0_eft_janus_z2_global_souriau_orbit_quantization_gate import (
    build_payload as souriau,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_gate import (
    build_payload as ll_flux,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_ethroat_quantum_topology_frontier_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_ethroat_quantum_topology_frontier_gate.md"


def _safe_payload(factory) -> dict:
    try:
        return factory()
    except Exception as exc:  # keep frontier audit non-destructive
        return {"status": "unavailable", "error": type(exc).__name__, "message": str(exc)}


def build_payload() -> dict:
    route_payloads = {
        "charge_quantization": {
            "inputs": {
                "souriau": _safe_payload(souriau),
                "ll_flux": _safe_payload(ll_flux),
                "area_gap": _safe_payload(area_gap),
            },
            "derives_E_throat": False,
            "new_postulate_needed": True,
            "missing": [
                "nonzero compact KKS/boundary period",
                "flux unit q_LL or area gap normalization",
                "primitive sector law N=1 or unique N",
            ],
        },
        "vacuum_topological_energy": {
            "inputs": {"casimir": _safe_payload(casimir)},
            "derives_E_throat": False,
            "new_postulate_needed": True,
            "missing": [
                "field content on Sigma",
                "boundary conditions",
                "renormalized Casimir coefficient and sign",
                "self-consistent L/R_sigma extremum",
            ],
        },
        "strong_global_regularity": {
            "inputs": {"regularity": _safe_payload(regularity)},
            "derives_E_throat": False,
            "new_postulate_needed": False,
            "missing": [
                "regularity fixes dimensionless smoothness only",
                "homothety L -> lambda L remains unfixed",
            ],
        },
        "ll_brane_tension": {
            "inputs": {"uv_ll": _safe_payload(uv_ll), "horizon": _safe_payload(horizon)},
            "derives_E_throat": False,
            "new_postulate_needed": True,
            "missing": [
                "Janus-specific chi_LL selection",
                "worldvolume gauge normalization",
                "boundary state or quantization of LL tension",
            ],
        },
        "boundary_action_selector": {
            "inputs": {"global_action": _safe_payload(global_action)},
            "derives_E_throat": False,
            "new_postulate_needed": False,
            "missing": [
                "finite on-shell S(L) or V(L)",
                "boundary prescription for noncompact exact orbit",
                "unique stationary point dV/dL=0",
            ],
        },
    }
    derived_routes = [
        name for name, route in route_payloads.items() if route["derives_E_throat"]
    ]
    return {
        "status": "janus-z2-ethroat-quantum-topology-frontier-gate",
        "active_core": "S4_L_to_RP4_L_resolved_by_Sigma",
        "target": "derive E_throat so L/alpha become no-fit",
        "E_throat_equals_E_global_is_structurally_allowed": True,
        "routes": route_payloads,
        "derived_routes": derived_routes,
        "E_throat_derived_from_current_assets": bool(derived_routes),
        "can_build_candidate_quantum_topology_theory": True,
        "candidate_theory_status_if_built_now": "new_physical_postulate_not_current_janus_derivation",
        "minimal_new_axioms_if_one_builds_it": [
            "Sigma carries a quantized boundary phase space or flux",
            "the primitive sector is selected uniquely",
            "the resulting charge equals E_throat/E_global",
        ],
        "strict_no_fit_status": "blocked",
        "interpretation": (
            "A quantum/topological throat theory can be proposed, but current "
            "Janus/Z2 assets do not derive its symplectic unit, flux unit, "
            "vacuum coefficient, brane tension, or finite boundary potential. "
            "Therefore it would be a new theory layer, not a completed Janus "
            "no-fit derivation."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 E_throat Quantum/Topology Frontier Gate",
        "",
        f"E_throat = E_global structurally allowed: `{payload['E_throat_equals_E_global_is_structurally_allowed']}`",
        f"E_throat derived from current assets: `{payload['E_throat_derived_from_current_assets']}`",
        f"Can build candidate throat quantum theory: `{payload['can_build_candidate_quantum_topology_theory']}`",
        f"Candidate status if built now: `{payload['candidate_theory_status_if_built_now']}`",
        f"Strict no-fit status: `{payload['strict_no_fit_status']}`",
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(
            f"- `{name}`: derives_E_throat=`{route['derives_E_throat']}`, "
            f"new_postulate_needed=`{route['new_postulate_needed']}`; "
            f"missing={', '.join(route['missing'])}"
        )
    lines.extend(["", "## Interpretation", "", payload["interpretation"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
