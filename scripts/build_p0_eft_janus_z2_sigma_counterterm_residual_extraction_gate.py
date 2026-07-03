from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate.json")


def build_payload() -> dict:
    declared = {
        "nonlinear_residual_closure_imported": True,
        "local_density_basis_gate_declared": True,
        "residual_one_form_decomposition_gate_declared": True,
        "residual_integrability_gate_declared": True,
        "boundary_variation_bibliography_checked": True,
        "residual_one_form_declared": True,
        "residual_integrability_condition_declared": True,
        "counterterm_primitive_declared": True,
        "uniqueness_transport_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "residual_one_form_explicit": False,
        "residual_integrability_proved": False,
        "counterterm_primitive_integrated": False,
        "L_ct_local_expansion_derived": False,
        "L_ct_ready_for_density_expansion_gate": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-residual-extraction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "active Janus Sigma nonlinear residual closure gate",
            "active counterterm local density basis gate",
            "active counterterm residual one-form decomposition gate",
            "active counterterm residual integrability gate",
            "Gibbons-Hawking-York boundary variation method",
            "Brown-York boundary stress/counterterm method",
            "well-posed variational principle boundary-term literature",
        ],
        "bibliography_result": (
            "Standard boundary-variation literature supplies the method: isolate the "
            "boundary residual one-form, prove exactness/integrability, and integrate "
            "a local primitive. It does not provide the active Janus/Sigma primitive."
        ),
        "declared": declared,
        "closure": closure,
        "structural_formulae": {
            "residual_one_form": "delta S_res = integral_Sigma R_A(q) delta q^A",
            "counterterm_condition": "delta S_ct = - delta S_res",
            "primitive_condition": "L_ct exists locally when R_A(q) dq^A is exact",
        },
        "forbidden": [
            "new fitted counterterm coefficient",
            "manual L_ct ansatz promoted as derived",
            "observational radius fit",
            "legacy Z4 counterterm import",
        ],
        "counterterm_residual_extraction_ledger_declared": all(declared.values()),
        "counterterm_residual_extraction_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "extract_explicit_residual_one_form_from_nonlinear_closure",
            "pass_counterterm_residual_one_form_decomposition_gate",
            "pass_counterterm_residual_integrability_gate",
            "prove_residual_one_form_integrable",
            "integrate_unique_counterterm_primitive",
            "express_L_ct_in_local_density_basis",
            "feed_L_ct_to_counterterm_density_expansion_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Residual Extraction Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_residual_extraction_ledger_declared']}`",
        f"Extraction ready: `{payload['counterterm_residual_extraction_ready']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
