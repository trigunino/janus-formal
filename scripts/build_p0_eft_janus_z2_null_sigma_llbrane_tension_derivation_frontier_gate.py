from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_worldvolume_tension_selection_gate import (
    build_payload as build_worldvolume_selection,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_pt_boundary_state_condition_gate import (
    build_payload as build_pt_boundary_state,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_gate import (
    build_payload as build_flux_quantization,
)

REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate.json"
)


def build_payload() -> dict:
    worldvolume = build_worldvolume_selection()
    pt_boundary = build_pt_boundary_state()
    flux_quantization = build_flux_quantization()
    closure = {
        "LL_brane_worldvolume_action_available_in_bibliography": True,
        "horizon_straddling_mechanism_available": True,
        "mass_as_function_of_tension_available": True,
        "local_worldvolume_tension_selection_exhausted": not worldvolume[
            "worldvolume_selection_ready"
        ],
        "Janus_specific_LL_brane_action_adopted": False,
        "chi_LL_equation_of_state_derived": False,
        "chi_LL_boundary_state_or_quantization_derived": (
            pt_boundary["PT_boundary_state_selects_chi"]
            or flux_quantization["flux_quantization_selects_chi"]
        ),
        "chi_LL_abs_inverse_m_numeric_available": False,
    }
    return {
        "status": "janus-z2-null-sigma-llbrane-tension-derivation-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "extension_status": "explicit_LL_brane_source_frontier",
        "bibliography": {
            "ER_bridge_LL_source": "Guendelman-Kaganovich-Nissimov-Pacheva arXiv:0904.3198",
            "LL_wormholes": "Guendelman-Kaganovich-Nissimov-Pacheva arXiv:0904.0401",
            "ER_revisited": "Guendelman-Nissimov-Pacheva arXiv:1611.04336",
        },
        "known_relations": {
            "dynamical_tension": "chi_LL is a worldvolume dynamical degree, not an ad hoc Nambu-Goto constant",
            "mass_relation": "m = 1/(16*pi*abs(chi_LL))",
            "radius_relation": "R_s = 1/(8*pi*abs(chi_LL))",
        },
        "worldvolume_tension_selection": {
            "status": worldvolume["status"],
            "worldvolume_selection_ready": worldvolume["worldvolume_selection_ready"],
            "blocked_by": worldvolume["blocked_by"],
            "interpretation": worldvolume["interpretation"],
        },
        "PT_boundary_state_condition": {
            "status": pt_boundary["status"],
            "PT_boundary_state_selects_chi": pt_boundary[
                "PT_boundary_state_selects_chi"
            ],
            "blocked_by": pt_boundary["blocked_by"],
            "interpretation": pt_boundary["interpretation"],
        },
        "flux_quantization": {
            "status": flux_quantization["status"],
            "flux_quantization_selects_chi": flux_quantization[
                "flux_quantization_selects_chi"
            ],
            "blocked_by": flux_quantization["blocked_by"],
            "interpretation": flux_quantization["interpretation"],
        },
        "closure": closure,
        "chi_LL_derivation_ready": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "next_required": [
            "adopt_or_derive_Janus_specific_LL_brane_worldvolume_action",
            "derive_chi_LL_equation_of_state_or_boundary_state_condition",
            "derive_chi_LL_abs_inverse_m_without_observational_fit",
        ],
        "forbidden_shortcuts": [
            "do_not_set_chi_LL_by_BAO_CMB_or_H0_fit",
            "do_not_identify_dynamical_tension_with_fixed_constant_without_state_condition",
            "do_not_promote_LL_brane_extension_as_strict_no_extension_model",
        ],
        "verdict": (
            "The LL-brane literature closes the bridge source consistency and the "
            "mass-radius relation in terms of chi_LL. It does not provide the Janus "
            "value of chi_LL. The remaining blocker is the Janus-specific tension "
            "selection law."
        ),
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Tension Derivation Frontier Gate",
        "",
        payload["verdict"],
        "",
        f"chi_LL derivation ready: `{payload['chi_LL_derivation_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
