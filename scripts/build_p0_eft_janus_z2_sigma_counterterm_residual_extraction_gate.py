from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_integrability_gate import (
    build_payload as build_integrability_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_one_form_decomposition_gate import (
    build_payload as build_one_form_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_local_density_basis_gate import (
    build_payload as build_local_density_basis_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_primitive_integration_gate import (
    build_payload as build_primitive_integration_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate.json")


def _first_blocker(*payloads: dict) -> str:
    for payload in payloads:
        blocker = payload.get("primary_blocker")
        if blocker and blocker != "none":
            return blocker
    return "counterterm_residual_one_form_exactness_and_primitive"


def build_payload() -> dict:
    one_form = build_one_form_payload()
    integrability = build_integrability_payload()
    basis = build_local_density_basis_payload()
    primitive = build_primitive_integration_payload(integrability_payload=integrability)
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
    counterterm_primitive_integrated = primitive["counterterm_primitive_integration_ready"]
    local_expansion_derived = (
        counterterm_primitive_integrated
        and basis["closure"]["L_ct_local_expansion_derived"]
    )
    closure = {
        "residual_one_form_explicit": one_form["closure"]["residual_one_form_components_explicit"],
        "residual_integrability_proved": integrability["closure"]["residual_one_form_exact"],
        "counterterm_primitive_integrated": counterterm_primitive_integrated,
        "L_ct_local_expansion_derived": local_expansion_derived,
        "L_ct_ready_for_density_expansion_gate": local_expansion_derived
        and basis["closure"]["L_ct_ready_for_density_expansion_gate"],
    }
    ready = all(declared.values()) and all(closure.values())
    primary_blocker = "none" if ready else _first_blocker(one_form, integrability, basis)
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
        "upstream_frontiers": {
            "one_form_decomposition": {
                "gate": one_form["status"],
                "ready": one_form["counterterm_residual_one_form_decomposition_ready"],
                "closure": one_form["closure"],
                "primary_blocker": one_form.get("primary_blocker", "counterterm_residual_channels"),
            },
            "integrability": {
                "gate": integrability["status"],
                "ready": integrability["counterterm_residual_integrability_ready"],
                "closure": integrability["closure"],
                "primary_blocker": integrability.get("primary_blocker", "counterterm_residual_exactness"),
            },
            "local_density_basis": {
                "gate": basis["status"],
                "ready": basis["counterterm_local_density_basis_ready"],
                "closure": basis["closure"],
                "primary_blocker": basis.get("primary_blocker", "counterterm_local_density_basis"),
            },
            "primitive_integration": {
                "gate": primitive["status"],
                "ready": primitive["counterterm_primitive_integration_ready"],
                "current_frontier": primitive["current_frontier"],
                "primary_blocker": primitive.get("primary_blocker", "counterterm_primitive_integration"),
            },
        },
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
        "counterterm_residual_extraction_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
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
    ]
    lines.extend(["", "## Current Frontier"])
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
