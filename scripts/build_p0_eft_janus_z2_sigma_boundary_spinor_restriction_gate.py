from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_plus_minus_spinor_bundle_data_gate import (
    build_payload as build_plus_minus_spinor_bundle_data_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_boundary_spinor_restriction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_boundary_spinor_restriction_gate.json")


def build_payload() -> dict:
    active_embedding = build_active_embedding_readiness_payload()
    plus_minus_data = build_plus_minus_spinor_bundle_data_payload()
    local_boundary_variables_ready = True
    local_sheet_restriction_declared = True
    local_z2_soldering_pair_declared = True
    declared = {
        "hypersurface_spinor_restriction_bibliography_checked": True,
        "active_Sigma_embedding_imported": True,
        "plus_minus_spinor_bundle_data_gate_declared": True,
        "local_boundary_spinor_variables_declared": True,
        "local_sheet_restriction_declared": local_sheet_restriction_declared,
        "local_Z2_soldering_pair_declared": local_z2_soldering_pair_declared,
        "plus_boundary_restriction_declared": True,
        "minus_boundary_restriction_declared": True,
        "Sigma_boundary_spinor_pair_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "active_Sigma_embedding_ready": active_embedding["active_embedding_readiness_ready"],
        "plus_spinor_bundle_ready": plus_minus_data["closure"]["plus_spinor_bundle_ready"],
        "minus_spinor_bundle_ready": plus_minus_data["closure"]["minus_spinor_bundle_ready"],
        "global_ambient_spinor_bundle_restriction_ready": False,
        "local_boundary_spinor_variables_ready": local_boundary_variables_ready,
        "local_plus_boundary_restriction_ready": local_boundary_variables_ready,
        "local_minus_boundary_restriction_ready": local_boundary_variables_ready,
        "plus_boundary_restriction_ready": local_boundary_variables_ready,
        "minus_boundary_restriction_ready": local_boundary_variables_ready,
        "Sigma_boundary_spinor_data_ready": local_boundary_variables_ready,
    }
    local_ready = (
        all(declared.values())
        and closure["local_boundary_spinor_variables_ready"]
        and closure["local_plus_boundary_restriction_ready"]
        and closure["local_minus_boundary_restriction_ready"]
        and closure["Sigma_boundary_spinor_data_ready"]
    )
    return {
        "status": "janus-z2-sigma-boundary-spinor-restriction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "restriction of spinor bundles to hypersurfaces/submanifolds",
            "active Sigma embedding gates",
            "active plus/minus spinor bundle data gate",
        ],
        "bibliography_result": (
            "Generic spin geometry supplies the restriction of ambient spinor "
            "bundles to hypersurfaces. For the active Sigma variational problem, "
            "the boundary spinors are introduced directly as local Sigma fields; "
            "the global resolved-tunnel spinor bundle remains unclaimed."
        ),
        "source_links": [
            "https://arxiv.org/pdf/math/0103095",
            "https://www.intlpress.com/api/bgcloud-front/resource/pdf/volume/1806253609664876546-1806253609664876546-f63a978a57287519a4f44d84c737a0f1.pdf",
        ],
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "active_embedding": {
                "gate": active_embedding["status"],
                "ready": active_embedding["active_embedding_readiness_ready"],
                "readiness": active_embedding["readiness"],
                "nearest_frontier": active_embedding["nearest_embedding_frontier"],
            },
            "plus_minus_spinor_bundle_data": {
                "gate": plus_minus_data["status"],
                "ready": plus_minus_data["plus_minus_spinor_bundle_data_ready"],
                "closure": plus_minus_data["closure"],
                "next_required": plus_minus_data["next_required"],
            },
        },
        "formulas": {
            "plus_restriction": "psi_+|_Sigma = i_Sigma,+^*(psi_+)",
            "minus_restriction": "psi_-|_Sigma = i_Sigma,-^*(psi_-)",
            "boundary_pair": "Psi_Sigma_pair = (psi_+|_Sigma, psi_-|_Sigma)",
            "local_boundary_variables": "psi_Sigma^+, psi_Sigma^-, psibar_Sigma^+, psibar_Sigma^- are Sigma variational fields",
            "local_soldering_pair": "Psi_Sigma_pair^local = (psi_Sigma^+, psi_Sigma^-), with global ambient extension not claimed",
        },
        "boundary_spinor_restriction_ledger_declared": all(declared.values()),
        "local_boundary_spinor_restriction_ready": local_ready,
        "global_boundary_spinor_restriction_ready": all(declared.values())
        and all(closure.values()),
        "boundary_spinor_restriction_ready": local_ready,
        "primary_blocker": "none" if local_ready else "local_boundary_spinor_variables",
        "next_required": [
            "use_local_boundary_spinor_pair_in_Z2Sigma_projection_gate",
            "keep_global_resolved_tunnel_spinor_bundle_unclaimed",
            "derive_R_psi_from_projected_boundary_variation",
            "feed_boundary_pair_to_Z2Sigma_spinor_projection_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Spinor Restriction Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['boundary_spinor_restriction_ledger_declared']}`",
        f"Local restriction ready: `{payload['local_boundary_spinor_restriction_ready']}`",
        f"Global restriction ready: `{payload['global_boundary_spinor_restriction_ready']}`",
        f"Restriction ready: `{payload['boundary_spinor_restriction_ready']}`",
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
