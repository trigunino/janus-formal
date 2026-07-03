from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_law_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_law_gate.json")


def build_payload() -> dict:
    declared = {
        "Janus_tunnel_bibliography_checked": True,
        "thin_shell_FRW_wormhole_bibliography_checked": True,
        "throat_radius_variable_declared": True,
        "candidate_comoving_throat_ansatz_declared": True,
        "active_no_fit_derivation_required": True,
        "observational_fit_for_radius_forbidden": True,
    }
    closure = {
        "Janus_action_or_topology_derives_radius_law": False,
        "R_Sigma_of_a_ready": False,
        "R_Sigma_law_prediction_ready": False,
    }
    return {
        "status": "janus-z2-sigma-throat-radius-law-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Petit/Margnat/Zejli 2024, arXiv:2412.04644",
            "La Camera 2011, On thin-shell wormholes evolving in flat FRW spacetimes, arXiv:1102.5284",
            "generic Darmois-Israel thin-shell wormhole literature",
        ],
        "bibliography_result": (
            "Thin-shell FRW wormhole literature allows a physical throat radius of type a*R. "
            "This is only a candidate ansatz here; Janus Z2/Sigma must derive R_Sigma(a) "
            "from the resolved tunnel action/topology."
        ),
        "declared": declared,
        "closure": closure,
        "candidate_laws": {
            "comoving_throat": "R_Sigma(a) = a * R0",
            "fixed_physical_throat": "R_Sigma(a) = R0",
            "general_active_law": "R_Sigma(a) derived from Sigma action/topology",
        },
        "throat_radius_law_problem_declared": all(declared.values()),
        "throat_radius_law_closure_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "derive_R_Sigma_of_a_from_resolved_projective_tunnel_action_or_topology",
            "reject_or_promote_comoving_throat_ansatz_by_internal_geometry_not_fit",
            "propagate_R_Sigma_of_a_into_X_plus_minus_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Throat Radius Law Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Problem declared: `{payload['throat_radius_law_problem_declared']}`",
        f"Closure ready: `{payload['throat_radius_law_closure_ready']}`",
        "",
        "## Candidate Laws",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["candidate_laws"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
