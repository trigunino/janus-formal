from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_gate import (
    EMBEDDING_MANIFEST_PATH,
    build_payload as build_coframe_connection_pullback_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_bundle_projection_gate import (
    build_payload as build_spinor_bundle_projection_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate.json")


def build_payload(*, embedding_manifest_path: Path = EMBEDDING_MANIFEST_PATH) -> dict:
    coframe_connection = build_coframe_connection_pullback_payload(
        embedding_manifest_path=embedding_manifest_path
    )
    spinor_projection = build_spinor_bundle_projection_payload()
    declared = {
        "curved_Dirac_action_bibliography_checked": True,
        "Holst_fermion_coupling_bibliography_checked": True,
        "coframe_connection_pullback_gate_declared": True,
        "spinor_bundle_projection_gate_declared": True,
        "plus_minus_Dirac_actions_declared": True,
        "Z2_projected_Dirac_action_declared": True,
        "no_effective_fitted_mass_or_phase": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "coframe_connection_pullback_ready": coframe_connection[
            "coframe_connection_pullback_ready"
        ],
        "plus_minus_spinor_projection_ready": spinor_projection["closure"][
            "plus_minus_spinor_projection_ready"
        ],
        "plus_Dirac_action_reduced": False,
        "minus_Dirac_action_reduced": False,
        "Z2_projected_Dirac_action_ready": False,
        "plus_minus_matter_actions_ready": False,
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = "none"
    if not ready:
        if not coframe_connection["gate_passed"]:
            primary_blocker = coframe_connection["primary_blocker"]
        elif not spinor_projection["gate_passed"]:
            primary_blocker = spinor_projection["primary_blocker"]
        else:
            primary_blocker = "plus_minus_Dirac_action_reduction"
    return {
        "status": "janus-z2-sigma-projected-dirac-action-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "curved Dirac action in tetrad/spin-connection form",
            "Holst/Einstein-Cartan fermion coupling",
            "active coframe/connection and spinor projection gates",
        ],
        "bibliography_result": (
            "Generic literature supplies the first-order curved Dirac action and "
            "Holst fermion/torsion coupling. It does not reduce the active Janus "
            "plus/minus actions through the Z2/Sigma projector."
        ),
        "source_links": [
            "https://link.aps.org/doi/10.1103/PhysRevD.79.064029",
            "https://doi.org/10.1007/s10714-013-1552-7",
            "https://arxiv.org/pdf/1803.10621",
        ],
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "coframe_connection_pullback": {
                "gate": coframe_connection["status"],
                "ready": coframe_connection["coframe_connection_pullback_ready"],
                "primary_blocker": coframe_connection["primary_blocker"],
                "closure": coframe_connection["closure"],
                "next_required": coframe_connection["next_required"],
            },
            "spinor_bundle_projection": {
                "gate": spinor_projection["status"],
                "ready": spinor_projection["spinor_bundle_projection_ready"],
                "primary_blocker": spinor_projection["primary_blocker"],
                "closure": spinor_projection["closure"],
                "next_required": spinor_projection["next_required"],
            },
        },
        "formulas": {
            "plus_action": "S_D,+[e_+,omega_+,psi_+] with e_+,omega_+ pulled to active data",
            "minus_action": "S_D,-[e_-,omega_-,psi_-] with e_-,omega_- pulled to active data",
            "projection": "S_D^Z2Sigma = P_Z2Sigma(S_D,+, S_D,-; psi_Sigma^Z2)",
            "policy": "no fitted effective mass, boundary phase, or chiral angle",
        },
        "projected_dirac_action_reduction_ledger_declared": all(declared.values()),
        "projected_dirac_action_reduction_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "next_required": [
            "pass_coframe_connection_pullback_gate",
            "pass_spinor_bundle_projection_gate",
            "reduce_plus_Dirac_action",
            "reduce_minus_Dirac_action",
            "derive_Z2_projected_Dirac_action",
            "feed_projected_action_to_mass_term_from_action_gate",
            "feed_projected_action_to_matter_current_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projected Dirac Action Reduction Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['projected_dirac_action_reduction_ledger_declared']}`",
        f"Reduction ready: `{payload['projected_dirac_action_reduction_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
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
