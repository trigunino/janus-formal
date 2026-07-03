from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_torsion_pullback_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_torsion_pullback_readiness_gate.json")


def build_payload() -> dict:
    declared = {
        "active_embedding_from_radius_gate_imported": True,
        "coframe_connection_pullback_gate_imported": True,
        "torsion_pullback_on_sigma_gate_imported": True,
        "oriented_pullback_variation_commutation_gate_imported": True,
        "torsion_variation_transport_gate_imported": True,
        "Cartan_pullback_bibliography_checked": True,
    }
    readiness = {
        "active_embedding_ready": False,
        "coframe_connection_pullback_ready": False,
        "oriented_pullback_commutation_ready": True,
        "ambient_torsion_formula_ready": True,
        "Sigma_torsion_pullback_ready": False,
        "FLRW_irreducible_torsion_pullback_ready": False,
        "torsion_pullback_on_Sigma_ready": False,
        "torsion_pullback_variation_allowed_basis_ready": False,
        "torsion_pullback_variation_transport_ready": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-torsion-pullback-readiness-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Cartan first structure equation T^I = d e^I + omega^I_J wedge e^J",
            "first-order Palatini-Holst coframe/connection formalism",
            "differential-form pullback functoriality",
            "thin-shell oriented normal conventions",
        ],
        "source_links": [
            "https://link.aps.org/doi/10.1103/PhysRevD.105.064066",
            "https://ncatlab.org/nlab/show/Cartan%2Bstructural%2Bequations",
        ],
        "bibliography_result": (
            "Standard Cartan/form-pullback literature supplies the local torsion formula "
            "and pullback language. The active Janus input still has to supply the derived "
            "Sigma embedding and coframe/connection pullbacks before the torsion boundary "
            "variation can close."
        ),
        "declared": declared,
        "readiness": readiness,
        "closed": [
            "oriented_pullback_commutation_ready",
            "ambient_torsion_formula_ready",
        ],
        "still_open": [
            "active_embedding_ready",
            "coframe_connection_pullback_ready",
            "Sigma_torsion_pullback_ready",
            "FLRW_irreducible_torsion_pullback_ready",
            "torsion_pullback_variation_allowed_basis_ready",
            "torsion_pullback_variation_transport_ready",
        ],
        "torsion_pullback_readiness_ledger_declared": all(declared.values()),
        "torsion_pullback_readiness_ready": all(declared.values()) and all(readiness.values()),
        "next_required": [
            "close_active_tunnel_embedding_from_radius_gate",
            "close_coframe_connection_pullback_gate",
            "reduce_Sigma_torsion_pullback_to_FLRW_irreducible_basis",
            "feed_allowed_basis_to_tetrad_torsion_pullback_variation_transport_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Torsion Pullback Readiness Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['torsion_pullback_readiness_ledger_declared']}`",
        f"Readiness ready: `{payload['torsion_pullback_readiness_ready']}`",
        "",
        "## Closed",
    ]
    lines.extend(f"- `{item}`" for item in payload["closed"])
    lines.extend(["", "## Still Open"])
    lines.extend(f"- `{item}`" for item in payload["still_open"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
