from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_projection_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_projection_readiness_gate.json")


def build_payload() -> dict:
    declared = {
        "spinor_bundle_projection_gate_imported": True,
        "plus_minus_spinor_bundle_data_gate_imported": True,
        "boundary_spinor_restriction_gate_imported": True,
        "spinor_boundary_projection_map_gate_imported": True,
        "resolved_tunnel_Pin_lift_gate_imported": True,
        "spinor_projection_bibliography_checked": True,
    }
    readiness = {
        "generic_spinor_bundle_restriction_ready": True,
        "generic_APS_projection_formula_ready": True,
        "resolved_tunnel_Pin_lift_ready": False,
        "plus_minus_spinor_bundle_data_ready": False,
        "Sigma_boundary_spinor_data_ready": False,
        "Z2Sigma_projection_map_ready": False,
        "plus_minus_spinor_projection_ready": False,
    }
    return {
        "status": "janus-z2-sigma-spinor-projection-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "APS boundary spectral projection and eta invariant",
            "hypersurface spinor restriction in tetrad/spin-connection language",
            "local boundary spinor projector/idempotence conventions",
        ],
        "source_links": [
            "https://webhomes.maths.ed.ac.uk/~v1ranick/papers/aps001.pdf",
            "https://trautman.fuw.edu.pl/publications/Papers-in-pdf/78.pdf",
            "https://arxiv.org/pdf/2412.17396",
        ],
        "bibliography_result": (
            "Generic spinor restriction and APS/local projection formulae are available. "
            "The active Janus projection still needs the resolved tunnel Pin lift, plus/minus "
            "spinor bundle data, Sigma boundary spinors, and a proved Z2/Sigma projection map."
        ),
        "declared": declared,
        "readiness": readiness,
        "closed": [
            "generic_spinor_bundle_restriction_ready",
            "generic_APS_projection_formula_ready",
        ],
        "still_open": [
            "resolved_tunnel_Pin_lift_ready",
            "plus_minus_spinor_bundle_data_ready",
            "Sigma_boundary_spinor_data_ready",
            "Z2Sigma_projection_map_ready",
            "plus_minus_spinor_projection_ready",
        ],
        "formulae": {
            "boundary_restriction": "psi_pm|_Sigma = i_Sigma,pm^*(psi_pm)",
            "z2_projected_spinor": "psi_Sigma^Z2 = P_Z2Sigma(psi_+|_Sigma, psi_-|_Sigma, APS/Pin data)",
            "projection_idempotence": "P_Z2Sigma^2 = P_Z2Sigma",
            "projection_self_adjointness": "P_Z2Sigma^dagger = P_Z2Sigma",
        },
        "spinor_projection_readiness_ledger_declared": all(declared.values()),
        "spinor_projection_readiness_ready": all(declared.values()) and all(readiness.values()),
        "next_required": [
            "close_resolved_tunnel_Pin_lift_gate",
            "close_plus_minus_spinor_bundle_data_gate",
            "close_boundary_spinor_restriction_gate",
            "prove_Z2Sigma_projection_idempotent_and_self_adjoint",
            "feed_spinor_projection_to_projected_Dirac_action_readiness_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Spinor Projection Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['spinor_projection_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['spinor_projection_readiness_ready']}`",
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
