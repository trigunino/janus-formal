from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_rsigma_modulus_fixing_principles_gate import (
    build_payload as build_modulus_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_rsigma_observable_modulus_audit_gate import (
    build_payload as build_observable_modulus_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_law_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_throat_radius_law_gate.json")


def build_payload() -> dict:
    modulus = build_modulus_payload()
    observable_modulus = build_observable_modulus_payload()
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
        "R_Sigma_modulus_open": modulus["R_Sigma_modulus_open"],
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
        "modulus_fixing_principles": {
            "gate": modulus["status"],
            "fixed_by_known_internal_principle": modulus[
                "fixed_by_known_internal_principle"
            ],
            "primary_blocker": modulus["primary_blocker"],
            "next_physical_inputs": modulus["next_physical_inputs"],
        },
        "observable_modulus_audit": {
            "gate": observable_modulus["status"],
            "full_observable_RSigma_cancellation_proved": observable_modulus[
                "full_observable_RSigma_cancellation_proved"
            ],
            "scale_free_branch_can_continue_without_extension": observable_modulus[
                "scale_free_branch_can_be_pursued_without_extension"
            ],
            "official_dimensional_branch_requires_radius_or_scale_input": observable_modulus[
                "official_dimensional_branch_requires_radius_or_scale_input"
            ],
        },
        "throat_radius_law_problem_declared": all(declared.values()),
        "throat_radius_law_closure_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
        "derive_R_Sigma_of_a_from_resolved_projective_tunnel_action_or_topology",
        "reject_or_promote_comoving_throat_ansatz_by_internal_geometry_not_fit",
        "if_no_extension_allowed_continue_only_RSigma_free_scale_free_branch",
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
