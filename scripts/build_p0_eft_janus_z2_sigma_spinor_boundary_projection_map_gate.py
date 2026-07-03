from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate.json")


def build_payload() -> dict:
    declared = {
        "APS_projection_bibliography_checked": True,
        "local_boundary_projection_bibliography_checked": True,
        "boundary_spinor_restriction_gate_declared": True,
        "APS_Pin_lift_input_imported": True,
        "Z2_normal_orientation_input_imported": True,
        "projection_map_declared": True,
        "no_free_boundary_phase": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "Sigma_boundary_spinor_data_ready": False,
        "Sigma_APS_boundary_Pin_lift_closed": False,
        "Z2_normal_orientation_ready": False,
        "projection_idempotent_ready": False,
        "projection_self_adjoint_ready": False,
        "Z2Sigma_spinor_projection_ready": False,
    }
    return {
        "status": "janus-z2-sigma-spinor-boundary-projection-map-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "APS spectral boundary projectors for Dirac operators",
            "local MIT/chiral bag boundary projectors using normal Clifford action",
            "active Sigma APS/Pin and Z2 normal-orientation gates",
        ],
        "bibliography_result": (
            "Generic Dirac boundary theory supplies spectral and local projector "
            "machinery. It does not supply the active Janus Z2/Sigma projector or "
            "its fixed phase/sign conventions."
        ),
        "source_links": [
            "https://webhomes.maths.ed.ac.uk/~v1ranick/papers/aps001.pdf",
            "https://arxiv.org/html/2412.17396v1",
            "https://hal.science/hal-00021463/document",
        ],
        "declared": declared,
        "closure": closure,
        "formulas": {
            "projection_map": "psi_Sigma^Z2 = P_Z2Sigma(psi_+|_Sigma, psi_-|_Sigma, n_Z2, APS/Pin data)",
            "idempotence_guard": "P_Z2Sigma^2 = P_Z2Sigma",
            "adjoint_guard": "P_Z2Sigma^dagger = P_Z2Sigma",
            "phase_policy": "no fitted boundary phase or free chiral bag angle",
        },
        "spinor_boundary_projection_map_ledger_declared": all(declared.values()),
        "spinor_boundary_projection_map_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_boundary_spinor_restriction_gate",
            "close_sigma_APS_Pin_lift",
            "derive_Z2_normal_orientation",
            "prove_P_Z2Sigma_idempotent",
            "prove_P_Z2Sigma_self_adjoint",
            "feed_projection_map_to_spinor_bundle_projection_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Spinor Boundary Projection Map Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['spinor_boundary_projection_map_ledger_declared']}`",
        f"Projection map ready: `{payload['spinor_boundary_projection_map_ready']}`",
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
