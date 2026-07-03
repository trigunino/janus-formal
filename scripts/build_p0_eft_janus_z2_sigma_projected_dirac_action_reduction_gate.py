from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate.json")


def build_payload() -> dict:
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
        "coframe_connection_pullback_ready": False,
        "plus_minus_spinor_projection_ready": False,
        "plus_Dirac_action_reduced": False,
        "minus_Dirac_action_reduced": False,
        "Z2_projected_Dirac_action_ready": False,
        "plus_minus_matter_actions_ready": False,
    }
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
        "formulas": {
            "plus_action": "S_D,+[e_+,omega_+,psi_+] with e_+,omega_+ pulled to active data",
            "minus_action": "S_D,-[e_-,omega_-,psi_-] with e_-,omega_- pulled to active data",
            "projection": "S_D^Z2Sigma = P_Z2Sigma(S_D,+, S_D,-; psi_Sigma^Z2)",
            "policy": "no fitted effective mass, boundary phase, or chiral angle",
        },
        "projected_dirac_action_reduction_ledger_declared": all(declared.values()),
        "projected_dirac_action_reduction_ready": all(declared.values()) and all(closure.values()),
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
