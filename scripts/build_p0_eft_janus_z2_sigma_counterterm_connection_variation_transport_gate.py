from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_connection_variation_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_connection_variation_transport_gate.json")


def build_payload() -> dict:
    declared = {
        "coframe_connection_pullback_gate_declared": True,
        "torsion_pullback_on_sigma_gate_declared": True,
        "holst_nieh_yan_radial_block_gate_declared": True,
        "holst_nieh_yan_connection_variation_bibliography_checked": True,
        "connection_variation_basis_declared": True,
        "fixed_coframe_connection_variation_branch_declared": True,
        "delta_omega_to_delta_torsion_formula_declared": True,
        "delta_torsion_to_nieh_yan_variation_declared": True,
        "sigma_pullback_commutation_declared": True,
        "fixed_embedding_connection_pullback_variation_gate_declared": True,
        "z2_orientation_transport_declared": True,
        "no_fitted_transport_coefficient": True,
    }
    closure = {
        "sigma_pullback_ready": False,
        "delta_omega_to_delta_torsion_formula_proved": False,
        "nieh_yan_variation_transport_proved": False,
        "connection_variation_transport_ready": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-connection-variation-transport-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Cartan first structure equation",
            "Nieh-Yan torsional invariant",
            "Holst/Nieh-Yan relation in first-order gravity",
            "active torsion pullback on Sigma gate",
            "active fixed-embedding connection pullback variation gate",
        ],
        "bibliography_result": (
            "Primary geometry gives the fixed-coframe branch delta_omega T^I = "
            "delta omega^I_J wedge e^J and the Nieh-Yan torsion structure. It does "
            "not prove the active Sigma pullback/orientation transport."
        ),
        "declared": declared,
        "closure": closure,
        "formulae": {
            "fixed_coframe_torsion_variation": "delta_omega T^I = delta omega^I_J wedge e^J",
            "sigma_pullback": "delta_omega X_Sigma^*T^I = X_Sigma^*(delta omega^I_J wedge e^J)",
            "nieh_yan_density": "NY = T^I wedge T_I - e^I wedge e^J wedge R_IJ",
            "connection_channel_target": "R_omega extracted from delta_omega S_HolstNiehYan|_Sigma",
        },
        "forbidden": [
            "fitted transport coefficient",
            "torsion-free shortcut",
            "manual Sigma orientation sign",
            "legacy Z4 connection transport import",
        ],
        "counterterm_connection_variation_transport_ledger_declared": all(declared.values()),
        "counterterm_connection_variation_transport_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_torsion_pullback_on_Sigma_gate",
            "pass_fixed_embedding_connection_pullback_variation_gate",
            "prove_pullback_commutes_with_fixed_embedding_delta_omega",
            "prove_delta_omega_torsion_formula_on_Sigma",
            "derive_delta_omega_Nieh_Yan_boundary_variation",
            "feed_transport_to_connection_residual_channel_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Connection Variation Transport Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_connection_variation_transport_ledger_declared']}`",
        f"Transport ready: `{payload['counterterm_connection_variation_transport_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
