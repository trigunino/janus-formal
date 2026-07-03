from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_integrability_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_integrability_gate.json")


def build_payload() -> dict:
    declared = {
        "residual_one_form_decomposition_gate_declared": True,
        "covariant_phase_space_bibliography_checked": True,
        "variational_bicomplex_bibliography_checked": True,
        "field_space_exterior_derivative_declared": True,
        "channel_cross_derivative_matrix_declared": True,
        "z2_boundary_compatibility_declared": True,
        "no_fitted_exactness_condition": True,
    }
    closure = {
        "residual_one_form_components_explicit": False,
        "field_space_curl_computed": False,
        "channel_cross_derivatives_symmetric": False,
        "z2_boundary_compatibility_proved": False,
        "residual_one_form_exact": False,
        "ready_for_counterterm_primitive": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-residual-integrability-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "covariant phase space with boundaries",
            "relative variational bicomplex framework",
            "inverse problem / exactness in the variational bicomplex",
        ],
        "bibliography_result": (
            "The primary framework says a boundary residual one-form can be integrated "
            "only after its field-space curl/exactness obstruction is controlled. It "
            "does not close the active Janus/Sigma curl components."
        ),
        "declared": declared,
        "closure": closure,
        "integrability_condition": "d_field alpha_res = 0",
        "cross_derivative_template": "partial_A R_B - partial_B R_A = 0 for active Sigma channels",
        "forbidden": [
            "fitted exactness condition",
            "dropping a residual channel to force closure",
            "manual primitive before curl check",
            "legacy Z4 integrability import",
        ],
        "counterterm_residual_integrability_ledger_declared": all(declared.values()),
        "counterterm_residual_integrability_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_counterterm_residual_one_form_decomposition_gate",
            "compute_field_space_curl_of_alpha_res",
            "prove_cross_derivative_symmetry_between_channels",
            "prove_z2_boundary_compatibility_of_curl",
            "feed_exact_one_form_to_counterterm_primitive_extraction",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Residual Integrability Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_residual_integrability_ledger_declared']}`",
        f"Integrability ready: `{payload['counterterm_residual_integrability_ready']}`",
        "",
        f"Condition: `{payload['integrability_condition']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
