from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_sigma_boundary_variational_decomposition_gate import (
    build_payload as build_boundary_variation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate import (
    build_payload as build_spinor_residual_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_local_pin_reflection_intertwiner_gate import (
    build_payload as build_local_intertwiner_payload,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_spinor_soldering_equivariance_from_boundary_variation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_spinor_soldering_equivariance_from_boundary_variation_gate.json"
)


def build_payload() -> dict:
    boundary = build_boundary_variation_payload()
    spinor_residual = build_spinor_residual_payload()
    local_intertwiner = build_local_intertwiner_payload()

    declared = {
        "boundary_variational_decomposition_imported": boundary[
            "sigma_boundary_variational_package_declared"
        ],
        "spinor_residual_channel_imported": spinor_residual[
            "counterterm_spinor_residual_channel_ledger_declared"
        ],
        "local_U_Z2_sigma_imported": local_intertwiner[
            "local_pin_reflection_intertwiner_ready"
        ],
        "spinor_soldering_condition_declared": True,
        "free_spinor_phase_forbidden": True,
        "MIT_projector_assumption_forbidden": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "R_psi_explicit_from_boundary_variation": spinor_residual["closure"][
            "spinor_residual_coefficient_explicit"
        ],
        "R_psibar_explicit_from_boundary_variation": spinor_residual["closure"][
            "conjugate_spinor_residual_coefficient_explicit"
        ],
        "spinor_residual_compatible_with_U_Z2_projection": spinor_residual["closure"][
            "spinor_residual_compatible_with_projection"
        ],
        "soldering_residual_zero_derived": False,
        "physical_spinor_equivariance_psi_minus_equals_U_Z2_psi_plus": False,
    }
    ready = all(declared.values()) and all(closure.values())
    return {
        "status": "janus-z2-sigma-spinor-soldering-equivariance-from-boundary-variation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": declared,
        "closure": closure,
        "route": {
            "local_intertwiner": "U_Z2^Sigma := B_n",
            "boundary_variation_channel": "alpha_psi = integral_Sigma (R_psi delta psi + delta psibar R_psibar)",
            "soldering_condition": "R_psi=0 and R_psibar=0 imply psi_-|_Sigma = U_Z2^Sigma psi_+|_Sigma",
        },
        "forbidden": [
            "free spinor phase",
            "assume MIT projector as physical boundary condition",
            "fit spinor residual coefficient",
            "legacy Z4 monodromy input",
            "promote current parity before soldering residual is zero",
        ],
        "physical_spinor_equivariance_from_boundary_variation_ready": ready,
        "gate_passed": ready,
        "primary_blocker": "none"
        if ready
        else "spinor_soldering_boundary_variation_residual",
        "next_required": []
        if ready
        else [
            "compute_R_psi_from_projected_dirac_boundary_variation",
            "compute_R_psibar_from_projected_dirac_boundary_variation",
            "prove_spinor_residual_compatible_with_U_Z2_projection",
            "derive_soldering_residual_zero",
            "then_promote_physical_spinor_equivariance",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Spinor Soldering Equivariance From Boundary Variation Gate",
        "",
        f"Ready: `{payload['physical_spinor_equivariance_from_boundary_variation_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
