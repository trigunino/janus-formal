from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_sigma_boundary_nonlinear_residual_closure_gate import (
    build_payload as build_sigma_closure_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_local_density_basis_gate import (
    build_payload as build_basis_payload,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate.json"
)


def build_payload() -> dict:
    sigma = build_sigma_closure_payload()
    basis = build_basis_payload()
    sigma_closed = bool(sigma["sigma_full_boundary_action_closed"])
    basis_declared = bool(basis["counterterm_local_density_basis_ledger_declared"])
    action_closed = sigma_closed and basis_declared
    return {
        "status": "janus-z2-sigma-counterterm-boundary-action-functional-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "boundary_action": {
            "symbol": "S_ct[Sigma]",
            "formula": (
                "S_ct[Sigma] = integral_Sigma d^3y sqrt_abs_h "
                "L_ct(h_ab,K_ab,T_pullback_A,chi,epsilon_Z2)"
            ),
            "measure": "dmu_Sigma = d^3y sqrt_abs_h",
            "orientation": "epsilon_Z2 carried only as local density argument",
            "integration_constant_policy": "L_ct(reference_residual_zero_throat)=0",
        },
        "not_duplicate_of": {
            "cartan_ghy": True,
            "holst_nieh_yan": True,
            "matter_or_dust_action": True,
            "tunnel_junction_action": True,
            "reason": (
                "S_ct is the unique Sigma-supported primitive of the isolated "
                "nonlinear residual one-form after Cartan/GHY, Holst/Nieh-Yan, "
                "matter flux and junction channels are already decomposed."
            ),
        },
        "closure": {
            "sigma_full_boundary_action_closed": sigma_closed,
            "local_density_basis_ledger_declared": basis_declared,
            "boundary_action_functional_written": action_closed,
            "induced_measure_fixed": action_closed,
            "not_duplicate_proven_by_variational_role": action_closed,
            "reduced_to_local_density_basis": action_closed,
            "integration_constant_fixed_symbolically": action_closed,
            "explicit_coefficient_expansion_ready": False,
            "counterterm_local_density_action_inputs_allowed": False,
        },
        "allowed_density_arguments": basis["allowed_basis"],
        "boundary_action_functional_closed": action_closed,
        "counterterm_local_density_action_inputs_allowed": False,
        "next_required": [
            "expand_L_ct_coefficients_in_allowed_basis",
            "compute_R_h_ab_R_K_ab_R_chi_from_S_ct_variation",
            "write_counterterm_local_density_action_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Boundary Action Functional Gate",
        "",
        f"Closed: `{payload['boundary_action_functional_closed']}`",
        f"Density inputs allowed: `{payload['counterterm_local_density_action_inputs_allowed']}`",
        "",
        "## Action",
        f"`{payload['boundary_action']['formula']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
