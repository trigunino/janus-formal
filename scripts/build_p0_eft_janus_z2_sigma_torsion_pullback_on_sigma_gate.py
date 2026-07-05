from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate import (
    build_payload as build_coframe_connection_pullback_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_irreducible_torsion_pullback_gate import (
    build_payload as build_flrw_irreducible_torsion_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_torsion_pullback_on_sigma_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_torsion_pullback_on_sigma_gate.json")


def build_payload(*, flrw_irreducible_payload: dict | None = None) -> dict:
    coframe_connection = build_coframe_connection_pullback_payload()
    declared = {
        "torsion_pullback_bibliography_checked": True,
        "differential_form_pullback_imported": True,
        "Cartan_first_structure_equation_imported": True,
        "Sigma_embedding_required": True,
        "coframe_pullback_required": True,
        "connection_pullback_required": True,
        "coframe_connection_pullback_gate_declared": True,
        "Z2_normal_orientation_required": True,
        "observational_fit_forbidden": True,
    }
    sigma_embedding_ready = coframe_connection["readiness"]["active_embedding_ready"]
    coframe_pullback_ready = coframe_connection["readiness"]["coframe_pullback_ready"]
    connection_pullback_ready = coframe_connection["readiness"]["spin_connection_pullback_ready"]
    ambient_torsion_form_ready = coframe_pullback_ready and connection_pullback_ready
    sigma_torsion_ready = sigma_embedding_ready and ambient_torsion_form_ready
    flrw_irreducible = flrw_irreducible_payload or build_flrw_irreducible_torsion_payload(
        sigma_torsion_pullback_ready=sigma_torsion_ready,
    )
    flrw_irreducible_ready = flrw_irreducible["FLRW_irreducible_torsion_pullback_ready"]
    closure = {
        "cartan_torsion_formula_ready": True,
        "sigma_pullback_formula_ready": True,
        "Sigma_embedding_ready": sigma_embedding_ready,
        "coframe_pullback_ready": coframe_pullback_ready,
        "connection_pullback_ready": connection_pullback_ready,
        "ambient_torsion_form_ready": ambient_torsion_form_ready,
        "Sigma_torsion_pullback_ready": sigma_torsion_ready,
        "FLRW_irreducible_torsion_pullback_ready": flrw_irreducible_ready,
        "torsion_pullback_on_Sigma_ready": sigma_torsion_ready
        and flrw_irreducible_ready,
    }
    return {
        "status": "janus-z2-sigma-torsion-pullback-on-sigma-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Cartan first structure equation literature",
            "standard differential-form pullback references",
            "Riemann-Cartan hypersurface/submanifold literature",
            "active coframe/connection pullback gate",
        ],
        "bibliography_result": (
            "Generic geometry supplies pullback of differential forms and the torsion "
            "2-form T^I = d e^I + omega^I_J wedge e^J. It does not supply the active "
            "Janus Z2/Sigma embedding, coframe pullback, connection pullback, or Z2 orientation."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "coframe_connection_pullback": {
                "gate": coframe_connection["status"],
                "ready": coframe_connection["coframe_connection_pullback_readiness_ready"],
                "readiness": coframe_connection["readiness"],
                "still_open": coframe_connection["still_open"],
            },
            "flrw_irreducible_torsion_pullback": {
                "gate": flrw_irreducible["status"],
                "ready": flrw_irreducible_ready,
                "primary_blocker": flrw_irreducible["primary_blocker"],
                "current_frontier": flrw_irreducible["current_frontier"],
            },
        },
        "formulas": {
            "ambient_torsion": "T^I = d e^I + omega^I_J wedge e^J",
            "sigma_pullback": "T^I|_Sigma = X_Sigma^*(T^I)",
            "irreducible_split": "X_Sigma^*(T) -> trace_vector + axial_vector + tensor_torsion on Sigma",
        },
        "partial_subchannels": {
            "cartan_torsion_formula": {
                "ready": True,
                "status": "partial_only_not_sigma_pullback_ready",
                "formula": "T^I = d e^I + omega^I_J wedge e^J",
            },
            "pullback_formula": {
                "ready": True,
                "status": "partial_only_waiting_for_active_embedding_and_fields",
                "formula": "X_Sigma^*(T^I)",
            },
            "flrw_irreducible_split": {
                "ready": flrw_irreducible_ready,
                "status": "blocked_until_sigma_torsion_pullback_ready",
            },
        },
        "torsion_pullback_ledger_declared": all(declared.values()),
        "torsion_pullback_on_sigma_ready": all(declared.values()) and all(closure.values()),
        "current_frontier": [
            f"{key} = false"
            for key, ready in closure.items()
            if not ready
        ],
        "next_required": [
            "pass_active_tunnel_embedding_of_a_gate",
            "pass_coframe_connection_pullback_gate",
            "derive_coframe_pullback_to_Sigma",
            "derive_spin_connection_pullback_to_Sigma",
            "compute_ambient_torsion_form_from_Cartan_equation",
            "reduce_FLRW_irreducible_torsion_pullback",
            "feed_torsion_pullback_to_Immirzi_and_Holst_Nieh_Yan_gates",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Torsion Pullback On Sigma Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['torsion_pullback_ledger_declared']}`",
        f"Torsion pullback ready: `{payload['torsion_pullback_on_sigma_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
