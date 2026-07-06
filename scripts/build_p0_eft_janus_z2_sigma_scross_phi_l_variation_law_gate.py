from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_scross_transport_source_acceptance_gate import (
    build_payload as build_scross_acceptance,
)
from scripts.build_p0_eft_janus_z2_sigma_transport_compatibility_source_equation_gate import (
    build_payload as build_transport_source,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scross_phi_l_variation_law_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scross_phi_l_variation_law_gate.json"
)


def build_payload() -> dict:
    scross = build_scross_acceptance()
    transport_source = build_transport_source()
    closure = {
        "S_cross_transport_source_acceptance_gate_imported": True,
        "transport_compatibility_source_equation_gate_imported": True,
        "phi_map_variation_declared": True,
        "L_solder_variation_declared": True,
        "sector_diffeomorphism_covariance_declared": True,
        "boundary_terms_controlled": True,
        "determinant_factors_kept_outside_bridge": True,
        "same_bridge_for_stress_and_Qcross": bool(
            scross["closure"]["same_bridge_for_transport_and_Qcross_required"]
        ),
        "no_multiplier_route": bool(scross["closure"]["no_multiplier_route"]),
        "independent_S_cross_functional_found": bool(
            scross["closure"]["independent_S_cross_functional_found"]
        ),
        "plus_phi_L_variation_law_derived": False,
        "minus_phi_L_variation_law_derived": False,
        "plus_source_divergence_equation_derived": False,
        "minus_source_divergence_equation_derived": False,
        "plus_transport_compatibility_source_derived": False,
        "minus_transport_compatibility_source_derived": False,
    }
    template_keys = [
        "S_cross_transport_source_acceptance_gate_imported",
        "transport_compatibility_source_equation_gate_imported",
        "phi_map_variation_declared",
        "L_solder_variation_declared",
        "sector_diffeomorphism_covariance_declared",
        "boundary_terms_controlled",
        "determinant_factors_kept_outside_bridge",
        "same_bridge_for_stress_and_Qcross",
        "no_multiplier_route",
    ]
    ready_keys = [
        "independent_S_cross_functional_found",
        "plus_phi_L_variation_law_derived",
        "minus_phi_L_variation_law_derived",
        "plus_source_divergence_equation_derived",
        "minus_source_divergence_equation_derived",
        "plus_transport_compatibility_source_derived",
        "minus_transport_compatibility_source_derived",
    ]
    template_ready = all(closure[key] for key in template_keys)
    law_ready = template_ready and all(closure[key] for key in ready_keys)
    blockers = [key for key in ready_keys if not closure[key]]
    return {
        "status": "janus-z2-sigma-scross-phi-l-variation-law-gate",
        "route_status": "conditional_template_ready_waiting_for_independent_scross",
        "variation_identity_template": (
            "delta_{phi,L} S_cross -> E_phi,E_L; sector diffeomorphism Noether "
            "identity then yields D_plus S_plus=0 and D_minus S_minus=0"
        ),
        "closure": closure,
        "conditional_template_ready": template_ready,
        "phi_l_variation_law_ready": law_ready,
        "gate_passed": law_ready,
        "primary_blocker": "none" if law_ready else blockers[0],
        "blockers": blockers,
        "upstream": {
            "S_cross_acceptance": {
                "gate_passed": scross["gate_passed"],
                "source_acceptance_ready": scross["source_acceptance_ready"],
                "primary_blocker": scross["primary_blocker"],
            },
            "transport_source_equation": {
                "gate_passed": transport_source["gate_passed"],
                "source_derivation_ready": transport_source["source_derivation_ready"],
                "primary_blocker": transport_source["primary_blocker"],
            },
        },
        "feeds": {
            "plus_source_divergence_equation_derived": closure[
                "plus_source_divergence_equation_derived"
            ],
            "minus_source_divergence_equation_derived": closure[
                "minus_source_divergence_equation_derived"
            ],
            "plus_transport_compatibility_source_derived": closure[
                "plus_transport_compatibility_source_derived"
            ],
            "minus_transport_compatibility_source_derived": closure[
                "minus_transport_compatibility_source_derived"
            ],
        },
        "next_required": [
            "supply independent S_cross/S_couple functional",
            "vary S_cross with respect to phi and L",
            "show E_phi/E_L imply plus and minus divergence equations",
            "feed transport compatibility source equation gate",
        ],
        "verdict": (
            "The phi/L variation route is now isolated as a conditional theorem target. "
            "It cannot close until an independent S_cross functional is supplied."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma S_cross Phi/L Variation Law Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"Template: `{payload['variation_identity_template']}`",
        "",
        payload["verdict"],
        "",
        "## Closure",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closure"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
