from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_around_sigma_z2_cycle_transport_gate import (
    build_payload as build_around_sigma_payload,
)
from scripts.build_p0_eft_janus_complex_reality_boundary_variation_basis_gate import (
    build_payload as build_variation_basis_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_closed_boundary_two_cycle_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_closed_boundary_two_cycle_gate.md"


def build_payload() -> dict[str, Any]:
    around_sigma = build_around_sigma_payload()
    variation_basis = build_variation_basis_payload()
    cycle_candidates = {
        "throat_angular_S2": {
            "dimension": 2,
            "closed": True,
            "boundary_support": "Sigma angular section",
            "kks_relevance": "topological_support_only",
            "period_status": "not_evaluable_without_active_pullback_density",
        },
        "aroundSigma_Z2": {
            "dimension": 1,
            "closed": around_sigma["around_sigma_cycle_defined"],
            "boundary_support": "tunnel throat generator",
            "kks_relevance": "one_cycle_not_two_cycle",
            "period_status": "cannot_integrate_KKS_two_form_alone",
        },
        "aroundSigma_cross_frame_phase": {
            "dimension": 2,
            "closed": False,
            "boundary_support": "requires compact frame/phase direction",
            "kks_relevance": "candidate_only",
            "period_status": "blocked_until_compact_phase_derived",
        },
        "finite_coadjoint_orbit_two_sphere": {
            "dimension": 2,
            "closed": True,
            "boundary_support": "complex coadjoint orbit, not Sigma boundary",
            "kks_relevance": "global_orbit_only",
            "period_status": "nonzero_global_KKS_not_boundary_period",
        },
    }
    checks = {
        "around_sigma_z2_cycle_closed": around_sigma["around_sigma_z2_transport_closed"],
        "topological_throat_S2_closed": cycle_candidates["throat_angular_S2"]["closed"],
        "finite_coadjoint_orbit_two_cycle_closed": cycle_candidates[
            "finite_coadjoint_orbit_two_sphere"
        ]["closed"],
        "symbolic_boundary_variation_basis_ready": variation_basis[
            "symbolic_boundary_variation_basis_ready"
        ],
        "active_boundary_variation_basis_ready": variation_basis[
            "active_boundary_variation_basis_ready"
        ],
        "closed_KKS_phase_space_two_cycle_declared": False,
        "nonzero_KKS_pullback_period_computed": False,
    }
    topological_cycle_audit_ready = (
        checks["around_sigma_z2_cycle_closed"]
        and checks["topological_throat_S2_closed"]
        and checks["finite_coadjoint_orbit_two_cycle_closed"]
    )
    kks_boundary_two_cycle_ready = (
        topological_cycle_audit_ready
        and checks["active_boundary_variation_basis_ready"]
        and checks["closed_KKS_phase_space_two_cycle_declared"]
        and checks["nonzero_KKS_pullback_period_computed"]
    )
    return {
        "status": "janus-complex-reality-closed-boundary-two-cycle-gate",
        "active_core": "Z2_tunnel_Sigma",
        "checks": checks,
        "cycle_candidates": cycle_candidates,
        "topological_cycle_audit_ready": topological_cycle_audit_ready,
        "KKS_boundary_two_cycle_ready": kks_boundary_two_cycle_ready,
        "KKS_boundary_period_nonzero": False,
        "alpha_generated_now": False,
        "interpretation": (
            "The active Janus/Z2 tunnel supplies closed topology, including a "
            "throat angular S2 and an aroundSigma Z2 one-cycle. This is not yet "
            "a closed KKS phase-space two-cycle. The missing object is a compact "
            "two-cycle made of physical boundary variations with a nonzero "
            "pullback period of Omega_Sigma."
        ),
        "what_this_closes": [
            "closed_topological_throat_S2_identified",
            "aroundSigma_confirmed_as_Z2_one_cycle_not_KKS_two_cycle",
            "finite_coadjoint_orbit_two_cycle_separated_from_Sigma_boundary",
        ],
        "still_missing_for_integrality": [
            key
            for key in [
                "active_boundary_variation_basis_ready",
                "closed_KKS_phase_space_two_cycle_declared",
                "nonzero_KKS_pullback_period_computed",
            ]
            if not checks[key]
        ],
        "next_gate": "ComplexRealityActiveEmbeddingOrCompactPhaseGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Closed Boundary Two-Cycle Gate",
                "",
                f"Topological cycle audit ready: `{payload['topological_cycle_audit_ready']}`",
                f"KKS boundary two-cycle ready: `{payload['KKS_boundary_two_cycle_ready']}`",
                f"KKS boundary period nonzero: `{payload['KKS_boundary_period_nonzero']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                payload["interpretation"],
                "",
                "## Closed",
                "",
                *[f"- `{item}`" for item in payload["what_this_closes"]],
                "",
                "## Still Missing For Integrality",
                "",
                *[f"- `{item}`" for item in payload["still_missing_for_integrality"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
