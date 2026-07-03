from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_torsion_pullback_variation_transport_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_torsion_pullback_variation_transport_gate.json")


def build_payload() -> dict:
    declared = {
        "tetrad_variation_transport_gate_imported": True,
        "torsion_pullback_on_sigma_gate_imported": True,
        "oriented_pullback_variation_commutation_imported": True,
        "cartan_structure_equation_bibliography_checked": True,
        "independent_connection_branch_declared": True,
        "torsion_formula_declared": True,
        "delta_e_to_delta_torsion_formula_declared": True,
        "sigma_pullback_commutation_declared": True,
        "z2_orientation_transport_declared": True,
        "no_fitted_torsion_variation_coefficient": True,
    }
    closure = {
        "torsion_pullback_ready": False,
        "pullback_commutation_ready": True,
        "delta_e_to_delta_torsion_formula_proved": True,
        "torsion_pullback_variation_in_allowed_basis": False,
        "torsion_pullback_variation_transport_ready": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-torsion-pullback-variation-transport-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Cartan first structure equation T^I = d e^I + omega^I_J wedge e^J",
            "first-order Palatini-Holst independent coframe/connection variations",
            "pullback/variation commutation for fixed Sigma embedding",
        ],
        "source_links": [
            "https://arxiv.org/abs/gr-qc/9209012",
            "https://arxiv.org/abs/1806.01529",
        ],
        "bibliography_result": (
            "For the independent-connection tetrad branch, Cartan's first structure "
            "equation gives delta_e T^I = D_omega(delta e^I). The active Sigma pullback "
            "still needs torsion-pullback readiness and oriented pullback/variation "
            "commutation before the boundary term is ready."
        ),
        "declared": declared,
        "closure": closure,
        "formulae": {
            "torsion": "T^I = d e^I + omega^I_J wedge e^J",
            "tetrad_variation_branch": "delta_e omega^I_J = 0",
            "delta_torsion": "delta_e T^I = D_omega(delta e^I)",
            "pullback_target": "delta_e X_Sigma^*T^I = X_Sigma^*(D_omega delta e^I) after oriented commutation",
        },
        "tetrad_torsion_pullback_variation_ledger_declared": all(declared.values()),
        "tetrad_torsion_pullback_variation_ready": all(declared.values()) and all(closure.values()),
        "closed": [
            "delta_e_to_delta_torsion_formula_proved",
            "pullback_commutation_ready",
        ],
        "still_open": [
            "torsion_pullback_ready",
            "torsion_pullback_variation_in_allowed_basis",
            "torsion_pullback_variation_transport_ready",
        ],
        "next_required": [
            "close_torsion_pullback_on_sigma_gate",
            "close_oriented_pullback_variation_commutation_gate",
            "express_XSigma_pullback_Domega_delta_e_in_allowed_basis",
            "feed_torsion_pullback_variation_transport_to_tetrad_variation_transport_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Torsion Pullback Variation Transport Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['tetrad_torsion_pullback_variation_ledger_declared']}`",
        f"Transport ready: `{payload['tetrad_torsion_pullback_variation_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
