from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate import (
    EMBEDDING_MANIFEST_PATH,
    build_payload as build_projected_dirac_action_reduction_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_dirac_matter_action_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_dirac_matter_action_gate.json")


def build_payload(*, embedding_manifest_path: Path = EMBEDDING_MANIFEST_PATH) -> dict:
    reduction = build_projected_dirac_action_reduction_payload(
        embedding_manifest_path=embedding_manifest_path
    )
    declared = {
        "curved_Dirac_action_bibliography_checked": True,
        "Holst_fermion_bibliography_checked": True,
        "plus_minus_spinor_bundles_declared": True,
        "spinor_bundle_projection_gate_declared": True,
        "projected_Dirac_action_reduction_gate_declared": True,
        "tetrad_spin_connection_inputs_required": True,
        "plus_Dirac_action_declared": True,
        "minus_Dirac_action_declared": True,
        "Z2Sigma_projection_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "coframe_connection_pullback_ready": reduction["closure"][
            "coframe_connection_pullback_ready"
        ],
        "plus_spinor_data_ready": reduction["closure"][
            "plus_minus_spinor_projection_ready"
        ],
        "minus_spinor_data_ready": reduction["closure"][
            "plus_minus_spinor_projection_ready"
        ],
        "plus_matter_action_ready": reduction["closure"]["plus_Dirac_action_reduced"],
        "minus_matter_action_ready": reduction["closure"]["minus_Dirac_action_reduced"],
        "plus_minus_matter_actions_ready": reduction["closure"][
            "plus_minus_matter_actions_ready"
        ],
    }
    ready = all(declared.values()) and all(closure.values())
    blockers = [key for key, value in closure.items() if not value]
    return {
        "status": "janus-z2-sigma-plus-minus-dirac-matter-action-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "curved-spacetime Dirac action in tetrad/spin-connection formalism",
            "Einstein-Cartan/Holst fermion coupling literature",
            "active coframe/connection pullback gate",
            "active spinor bundle projection gate",
            "active projected Dirac action reduction gate",
        ],
        "bibliography_result": (
            "Generic first-order gravity supplies the curved Dirac action and its "
            "Holst/torsion coupling context. It does not supply the active Janus "
            "plus/minus spinor bundle data or the Z2/Sigma projection."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_projected_dirac_action_reduction": {
            "gate": reduction["status"],
            "ready": reduction["projected_dirac_action_reduction_ready"],
            "primary_blocker": reduction["primary_blocker"],
            "closure": reduction["closure"],
        },
        "formulas": {
            "plus_action": "S_D,+ = integral_M+ e_+ psi_bar_+ (i gamma_+^I e_I^mu D_mu^+ - m_+) psi_+",
            "minus_action": "S_D,- = integral_M- e_- psi_bar_- (i gamma_-^I e_I^mu D_mu^- - m_-) psi_-",
            "holst_context": "torsion/spin-connection variation couples Dirac axial current to Holst/Immirzi sector",
            "projection": "S_D^Z2Sigma = P_Z2Sigma(S_D,+, S_D,-, Sigma spinor boundary data)",
        },
        "plus_minus_dirac_matter_action_ledger_declared": all(declared.values()),
        "local_plus_minus_dirac_matter_action_ready": ready,
        "strict_full_embedding_dirac_matter_action_ready": False,
        "plus_minus_dirac_matter_action_ready": ready,
        "primary_blocker": "none" if ready else blockers[0],
        "next_required": [
            "pass_coframe_connection_pullback_gate",
            "derive_plus_minus_spinor_bundle_data_on_resolved_tunnel",
            "pass_spinor_bundle_projection_gate",
            "pass_projected_Dirac_action_reduction_gate",
            "derive_Z2Sigma_spinor_boundary_projection",
            "reduce_plus_minus_Dirac_actions",
            "feed_actions_to_plus_minus_Dirac_action_local_reduction_gate",
            "feed_actions_to_plus_minus_matter_current_gate",
            "feed_actions_to_bulk_stress_and_Dirac_Holst_vertex_gates",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Plus/Minus Dirac Matter Action Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['plus_minus_dirac_matter_action_ledger_declared']}`",
        f"Actions ready: `{payload['plus_minus_dirac_matter_action_ready']}`",
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
