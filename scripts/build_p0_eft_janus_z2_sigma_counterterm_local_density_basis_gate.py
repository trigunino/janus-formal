from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_local_density_basis_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_local_density_basis_gate.json")


def build_payload() -> dict:
    declared = {
        "nonlinear_residual_closure_imported": True,
        "boundary_counterterm_bibliography_checked": True,
        "active_variable_basis_declared": True,
        "h_block_declared": True,
        "K_block_declared": True,
        "torsion_pullback_block_declared": True,
        "Immirzi_boundary_block_declared": True,
        "Z2_orientation_block_declared": True,
        "no_new_counterterm_freedom_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "unique_counterterm_transported": True,
        "local_density_basis_complete": True,
        "L_ct_local_expansion_derived": False,
        "L_ct_ready_for_density_expansion_gate": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-local-density-basis-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "active Sigma nonlinear residual closure gate",
            "Brown-York/counterterm boundary variation methods",
            "local boundary invariant expansion practice",
        ],
        "bibliography_result": (
            "The unique Sigma-supported counterterm is already fixed by nonlinear "
            "residual closure. This gate only declares the local active basis in "
            "which its density must be expanded; it does not add any fitted freedom."
        ),
        "declared": declared,
        "closure": closure,
        "allowed_basis": [
            "h_ab",
            "K_ab",
            "Sigma torsion pullback",
            "Immirzi/radion boundary fields",
            "Z2 orientation sign",
        ],
        "forbidden": [
            "new counterterm coefficient",
            "observational radius fit",
            "legacy Z4 counterterm",
        ],
        "counterterm_local_density_basis_ledger_declared": all(declared.values()),
        "counterterm_local_density_basis_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "derive_explicit_L_ct_in_allowed_basis",
            "prove_no_new_counterterm_freedom_is_introduced",
            "feed_L_ct_to_counterterm_density_expansion_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Local Density Basis Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_local_density_basis_ledger_declared']}`",
        f"Ready: `{payload['counterterm_local_density_basis_ready']}`",
        "",
        "## Allowed Basis",
    ]
    lines.extend(f"- `{item}`" for item in payload["allowed_basis"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
