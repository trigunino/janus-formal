from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_closed_boundary_two_cycle_gate import (
    build_payload as build_two_cycle_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate import (
    build_payload as build_coframe_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_active_embedding_or_compact_phase_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_active_embedding_or_compact_phase_gate.md"


def build_payload() -> dict[str, Any]:
    cycle = build_two_cycle_payload()
    coframe = build_coframe_payload()
    active_embedding_route = {
        "route": "active_embedding_pullback_on_throat_S2",
        "requires": [
            "active_embedding_ready",
            "coframe_connection_pullback_ready",
            "active_boundary_variation_basis_ready",
            "Omega_Sigma_density_evaluable_on_S2",
        ],
        "checks": {
            "active_embedding_ready": coframe["readiness"]["active_embedding_ready"],
            "coframe_connection_pullback_ready": coframe["readiness"][
                "coframe_connection_pullback_ready"
            ],
            "active_boundary_variation_basis_ready": cycle["checks"][
                "active_boundary_variation_basis_ready"
            ],
            "Omega_Sigma_density_evaluable_on_S2": False,
        },
    }
    active_embedding_route["ready"] = all(active_embedding_route["checks"].values())
    compact_phase_route = {
        "route": "aroundSigma_cross_compact_frame_phase",
        "requires": [
            "aroundSigma_Z2_cycle_closed",
            "compact_frame_phase_derived",
            "phase_period_normalized",
            "KKS_cross_pairing_nonzero",
        ],
        "checks": {
            "aroundSigma_Z2_cycle_closed": cycle["checks"][
                "around_sigma_z2_cycle_closed"
            ],
            "compact_frame_phase_derived": False,
            "phase_period_normalized": False,
            "KKS_cross_pairing_nonzero": False,
        },
    }
    compact_phase_route["ready"] = all(compact_phase_route["checks"].values())
    return {
        "status": "janus-complex-reality-active-embedding-or-compact-phase-gate",
        "active_core": "Z2_tunnel_Sigma",
        "topological_cycle_audit_ready": cycle["topological_cycle_audit_ready"],
        "active_embedding_route": active_embedding_route,
        "compact_phase_route": compact_phase_route,
        "nonzero_KKS_boundary_period_route_ready": (
            active_embedding_route["ready"] or compact_phase_route["ready"]
        ),
        "alpha_generated_now": False,
        "interpretation": (
            "There are only two non-rustine exits left in this branch: evaluate "
            "Omega_Sigma on the active throat S2 from the resolved embedding, or "
            "derive a compact frame/phase direction that pairs with aroundSigma. "
            "Neither route is available from the current source set."
        ),
        "still_missing": {
            "active_embedding_route": [
                key for key, ok in active_embedding_route["checks"].items() if not ok
            ],
            "compact_phase_route": [
                key for key, ok in compact_phase_route["checks"].items() if not ok
            ],
        },
        "next_physical_inputs": [
            "active_embedding_values_for_Sigma_with_coframe_connection_pullback",
            "or Janus-derived compact frame/phase law with normalized period",
        ],
        "next_gate": "ComplexRealityAlphaStateLawVerdictGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Active Embedding Or Compact Phase Gate",
                "",
                f"Active embedding route ready: `{payload['active_embedding_route']['ready']}`",
                f"Compact phase route ready: `{payload['compact_phase_route']['ready']}`",
                f"Nonzero KKS period route ready: `{payload['nonzero_KKS_boundary_period_route_ready']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                payload["interpretation"],
                "",
                "## Next Physical Inputs",
                "",
                *[f"- `{item}`" for item in payload["next_physical_inputs"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
