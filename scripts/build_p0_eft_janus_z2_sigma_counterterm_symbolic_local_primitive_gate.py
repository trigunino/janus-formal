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
from scripts.derive_p0_eft_janus_z2_sigma_counterterm_residual_coefficients_partial import (
    build_payload as build_partial_coefficients_payload,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_symbolic_local_primitive.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_symbolic_local_primitive_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_symbolic_local_primitive_gate.json")


def build_payload(*, output_path: Path = OUTPUT_PATH) -> dict:
    sigma = build_sigma_closure_payload()
    basis = build_basis_payload()
    partial_coefficients = build_partial_coefficients_payload()
    sigma_closed = bool(sigma["sigma_full_boundary_action_closed"])
    basis_complete = bool(basis["closure"]["local_density_basis_complete"])
    symbolic_ready = sigma_closed and basis_complete
    primitive = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "counterterm_primitive_kind": "symbolic_local_field_space_primitive",
        "residual_one_form": (
            "alpha_res = R_h^{ab} dh_ab + R_K^{ab} dK_ab + "
            "R_T^A dT_A + R_chi dchi + R_Z2 depsilon_Z2"
        ),
        "primitive_formula": "L_ct = - integral_gamma alpha_res",
        "allowed_basis": basis["allowed_basis"],
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "fitted_counterterm_coefficient_used": False,
        "symbolic_primitive_exists": symbolic_ready,
        "coefficient_expansion_explicit": False,
        "partial_coefficient_expansion_ready": partial_coefficients["gate_passed"],
        "partial_coefficients_manifest": partial_coefficients["output_manifest"],
        "radial_profile_ready": False,
        "radial_profile_written": False,
    }
    output_written = False
    if symbolic_ready:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(primitive, indent=2), encoding="utf-8")
        output_written = True
    return {
        "status": "janus-z2-sigma-counterterm-symbolic-local-primitive-gate",
        "active_core": "Z2_tunnel_Sigma",
        "output_manifest": str(output_path),
        "declared": {
            "sigma_nonlinear_residual_closure_imported": True,
            "local_density_basis_imported": True,
            "field_space_primitive_formula_declared": True,
            "no_radial_value_claimed": True,
            "no_fitted_counterterm_coefficient": True,
        },
        "closure": {
            "sigma_full_boundary_action_closed": sigma_closed,
            "local_density_basis_complete": basis_complete,
            "symbolic_primitive_exists": symbolic_ready,
            "coefficient_expansion_explicit": False,
            "partial_coefficient_expansion_ready": partial_coefficients["gate_passed"],
            "radial_profile_ready": False,
        },
        "primitive": primitive,
        "symbolic_local_primitive_written": output_written,
        "symbolic_local_primitive_ready": symbolic_ready,
        "partial_coefficient_expansion_ready": partial_coefficients["gate_passed"],
        "partial_coefficients_manifest": partial_coefficients["output_manifest"],
        "gate_passed": symbolic_ready,
        "primary_blocker": "none" if symbolic_ready else "symbolic_counterterm_primitive_inputs",
        "next_required": [
            "expand_residual_coefficients_R_h_R_K_R_T_R_chi_in_allowed_basis",
            "prove_field_space_exactness_for_explicit_coefficients",
            "derive_counterterm_residual_scalar_contractions_inputs",
            "run_counterterm_lct_radial_profile_from_residual_contractions",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Symbolic Local Primitive Gate",
        "",
        f"Symbolic primitive ready: `{payload['symbolic_local_primitive_ready']}`",
        f"Radial profile ready: `{payload['closure']['radial_profile_ready']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
