from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_immirzi_profile_of_a_gate import (
    build_payload as build_immirzi_profile_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_torsion_pullback_on_sigma_gate import (
    build_payload as build_torsion_pullback_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_holst_nieh_yan_radial_block_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_holst_nieh_yan_radial_block_gate.json")


def build_payload(
    *,
    torsion_pullback_payload: dict | None = None,
    immirzi_profile_payload: dict | None = None,
) -> dict:
    torsion = torsion_pullback_payload or build_torsion_pullback_payload()
    immirzi = immirzi_profile_payload or build_immirzi_profile_payload()
    torsion_ready = bool(torsion["closure"]["torsion_pullback_on_Sigma_ready"])
    immirzi_ready = bool(immirzi["immirzi_profile_of_a_ready"])
    declared = {
        "Holst_Nieh_Yan_bibliography_checked": True,
        "torsion_required_for_nonzero_block_declared": True,
        "dynamic_Immirzi_boundary_variation_declared": True,
        "Sigma_torsion_pullback_required": True,
        "torsion_pullback_on_Sigma_gate_declared": True,
        "radial_embedding_variation_declared": True,
        "observational_fit_forbidden": True,
        "E_HolstNiehYan_functional_derivative_declared": True,
    }
    closure = {
        "E_HolstNiehYan_structural_reduction_ready": True,
        "Sigma_torsion_pullback_ready": torsion_ready,
        "Immirzi_radial_profile_ready": immirzi_ready,
        "E_HolstNiehYan_of_a_ready": torsion_ready and immirzi_ready,
    }
    return {
        "status": "janus-z2-sigma-holst-nieh-yan-radial-block-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Mercuri 2006, Fermions in Ashtekar-Barbero-Immirzi formalism",
            "Banerjee et al., Holst and Nieh-Yan terms in GR with torsion",
            "Nieh-Yan torsion boundary/topological invariant literature",
        ],
        "bibliography_result": (
            "The Holst/Nieh-Yan literature supports a torsion-dependent boundary/topological "
            "block and dynamic-Immirzi variation. It does not supply the active Janus/Sigma "
            "torsion pullback or radial Immirzi profile."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "torsion_pullback_on_Sigma": {
                "gate": torsion["status"],
                "ready": torsion["torsion_pullback_on_sigma_ready"],
                "current_frontier": torsion["current_frontier"],
            },
            "immirzi_profile_of_a": {
                "gate": immirzi["status"],
                "ready": immirzi["immirzi_profile_of_a_ready"],
                "primary_blocker": immirzi["primary_blocker"],
                "current_frontier": immirzi["current_frontier"],
            },
        },
        "structural_formula": (
            "E_HolstNiehYan = delta_RSigma S_HNY[Sigma] "
            "= delta_RSigma integral_Sigma gamma_Immirzi(R_Sigma) * NY_pullback(torsion, tetrad, connection)"
        ),
        "holst_nieh_yan_radial_ledger_declared": all(declared.values()),
        "holst_nieh_yan_radial_block_structurally_declared": all(declared.values())
        and closure["E_HolstNiehYan_structural_reduction_ready"],
        "holst_nieh_yan_radial_block_of_a_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else "torsion_pullback_on_Sigma"
            if not torsion_ready
            else "immirzi_profile_of_a"
        ),
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "derive_Sigma_torsion_pullback_from_active_Z2_Sigma_connection",
            "pass_torsion_pullback_on_Sigma_gate",
            "derive_Immirzi_radial_profile_from_active_boundary_action",
            "evaluate_delta_RSigma_of_Nieh_Yan_pullback",
            "propagate_E_HolstNiehYan_into_E_RSigma_block_sum",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Holst-Nieh-Yan Radial Block Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Structural block declared: `{payload['holst_nieh_yan_radial_block_structurally_declared']}`",
        f"Block of a ready: `{payload['holst_nieh_yan_radial_block_of_a_ready']}`",
        "",
        "## Structural Formula",
        f"`{payload['structural_formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
