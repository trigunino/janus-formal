from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_action_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_action_readiness_gate.json")


def build_payload() -> dict:
    declared = {
        "projected_Dirac_action_reduction_gate_imported": True,
        "coframe_connection_pullback_readiness_gate_imported": True,
        "spinor_bundle_projection_gate_imported": True,
        "projected_Dirac_matter_current_gate_imported": True,
        "curved_Dirac_Holst_bibliography_checked": True,
    }
    readiness = {
        "curved_Dirac_action_formula_ready": True,
        "Holst_fermion_coupling_formula_ready": True,
        "coframe_connection_pullback_ready": False,
        "plus_minus_spinor_projection_ready": False,
        "plus_Dirac_action_reduced": False,
        "minus_Dirac_action_reduced": False,
        "Z2_projected_Dirac_action_ready": False,
        "projected_Dirac_matter_current_ready": False,
    }
    return {
        "status": "janus-z2-sigma-projected-dirac-action-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "curved-spacetime Dirac action in tetrad/spin-connection form",
            "Einstein-Cartan/Holst fermion coupling",
            "Dirac U(1) Noether current from the projected action",
        ],
        "source_links": [
            "https://link.aps.org/doi/10.1103/PhysRevD.79.064029",
            "https://arxiv.org/html/2503.03918v2",
            "https://s3.cern.ch/inspire-prod-files-d/d0a75bfac1295febe61b60f90aef7505",
        ],
        "bibliography_result": (
            "The standard curved Dirac action and Holst fermion coupling are available. "
            "The active Janus reduction still needs coframe/connection pullbacks and "
            "the Z2/Sigma spinor projection."
        ),
        "declared": declared,
        "readiness": readiness,
        "closed": [
            "curved_Dirac_action_formula_ready",
            "Holst_fermion_coupling_formula_ready",
        ],
        "still_open": [
            "coframe_connection_pullback_ready",
            "plus_minus_spinor_projection_ready",
            "plus_Dirac_action_reduced",
            "minus_Dirac_action_reduced",
            "Z2_projected_Dirac_action_ready",
            "projected_Dirac_matter_current_ready",
        ],
        "formulae": {
            "curved_Dirac": "S_D = integral e psibar(i gamma^I e_I^mu D_mu - m) psi",
            "Holst_fermion": "Holst/Einstein-Cartan coupling supplies torsion-spin terms after connection variation",
            "projected_action": "S_D^Z2Sigma = P_Z2Sigma(S_D,+, S_D,-; psi_Sigma^Z2)",
        },
        "projected_dirac_action_readiness_ledger_declared": all(declared.values()),
        "projected_dirac_action_readiness_ready": all(declared.values()) and all(readiness.values()),
        "next_required": [
            "close_coframe_connection_pullback_readiness_gate",
            "close_spinor_bundle_projection_gate",
            "reduce_plus_and_minus_Dirac_actions",
            "derive_Z2_projected_Dirac_action",
            "feed_projected_action_to_projected_Dirac_matter_current_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projected Dirac Action Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['projected_dirac_action_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['projected_dirac_action_readiness_ready']}`",
        "",
        "## Closed",
    ]
    lines.extend(f"- `{item}`" for item in payload["closed"])
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
