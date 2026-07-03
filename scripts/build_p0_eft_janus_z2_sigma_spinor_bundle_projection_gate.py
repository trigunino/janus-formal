from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_bundle_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_bundle_projection_gate.json")


def build_payload() -> dict:
    declared = {
        "spinor_bundle_bibliography_checked": True,
        "APS_boundary_spinor_bibliography_checked": True,
        "plus_minus_spinor_bundle_data_gate_declared": True,
        "boundary_spinor_restriction_gate_declared": True,
        "spinor_boundary_projection_map_gate_declared": True,
        "plus_minus_spinor_bundles_declared": True,
        "Sigma_boundary_restriction_declared": True,
        "Z2Sigma_spinor_projection_declared": True,
        "APS_Pin_lift_input_imported": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_spinor_bundle_ready": False,
        "minus_spinor_bundle_ready": False,
        "Sigma_boundary_spinor_data_ready": False,
        "Z2Sigma_spinor_projection_ready": False,
        "plus_minus_spinor_projection_ready": False,
    }
    return {
        "status": "janus-z2-sigma-spinor-bundle-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "spinor bundles on spin manifolds and restrictions to hypersurfaces",
            "Atiyah-Patodi-Singer boundary conditions for Dirac operators",
            "active plus/minus spinor bundle data gate",
            "active boundary spinor restriction gate",
            "active Z2/Sigma spinor boundary projection map gate",
            "active Sigma APS/Pin lift and trace-regularization gates",
        ],
        "bibliography_result": (
            "Generic spin geometry supplies spinor bundles, boundary restriction "
            "machinery, and APS boundary projectors. It does not supply the active "
            "Janus plus/minus spinor bundles or the Z2/Sigma projection map."
        ),
        "source_links": [
            "https://webhomes.maths.ed.ac.uk/~v1ranick/papers/aps001.pdf",
            "https://arxiv.org/pdf/math/0103095",
            "https://ncatlab.org/nlab/files/Milnor-SpinStructures.pdf",
        ],
        "declared": declared,
        "closure": closure,
        "formulas": {
            "plus_minus_spinors": "S_pm -> M_pm, psi_pm in Gamma(S_pm)",
            "boundary_restriction": "psi_pm|_Sigma = i_Sigma^*(psi_pm)",
            "z2_projection": "psi_Sigma^Z2 = P_Z2Sigma(psi_+|_Sigma, psi_-|_Sigma, APS/Pin data)",
        },
        "spinor_bundle_projection_ledger_declared": all(declared.values()),
        "spinor_bundle_projection_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_sigma_APS_Pin_lift_obligation_gates",
            "pass_plus_minus_spinor_bundle_data_gate",
            "pass_boundary_spinor_restriction_gate",
            "pass_spinor_boundary_projection_map_gate",
            "derive_plus_minus_spinor_bundles_on_resolved_tunnel",
            "derive_boundary_restriction_of_spinors_to_Sigma",
            "derive_Z2Sigma_spinor_projection",
            "feed_spinor_projection_to_plus_minus_Dirac_matter_action_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Spinor Bundle Projection Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['spinor_bundle_projection_ledger_declared']}`",
        f"Projection ready: `{payload['spinor_bundle_projection_ready']}`",
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
