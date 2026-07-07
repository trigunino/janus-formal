from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_relation_audit_gate import (
    build_payload as build_relation_audit,
)

REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_gate.json"
)


def build_payload() -> dict:
    relation = build_relation_audit()
    closure = {
        "aroundSigma_cycle_available": True,
        "Z2_generator_cycle_available": True,
        "worldvolume_gauge_flux_declared": True,
        "integer_flux_condition_formulated": True,
        "flux_quantum_normalization_derived": relation["closure"][
            "worldvolume_charge_normalization_derived"
        ],
        "chi_LL_flux_relation_derived": relation["flux_relation_closes_chi"],
        "chi_LL_abs_inverse_m_selected": relation["flux_relation_closes_chi"],
    }
    return {
        "status": "janus-z2-null-sigma-llbrane-flux-quantization-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "extension_status": "explicit_LL_brane_source_frontier",
        "candidate_quantization": {
            "cycle": "aroundSigma maps to the active Z2 generator",
            "flux": "integral_{aroundSigma} A_LL or dual worldvolume flux",
            "integer_condition": "Phi_LL/(2*pi) = n",
            "risk": "chi_LL is a density/measure ratio, so flux integrality alone may quantize only chi_LL*R_s or a dimensionless charge",
        },
        "relation_audit": {
            "status": relation["status"],
            "flux_relation_closes_chi": relation["flux_relation_closes_chi"],
            "blocked_by": relation["blocked_by"],
            "topology": relation["topology"],
            "conditional_flux_algebra": relation["conditional_flux_algebra"],
            "interpretation": relation["interpretation"],
        },
        "closure": closure,
        "flux_quantization_selects_chi": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "interpretation": (
            "The active aroundSigma cycle gives a plausible place for a worldvolume "
            "flux quantization law. However, the current data do not derive the flux "
            "quantum normalization or a non-circular relation from the integer flux "
            "to chi_LL_abs_inverse_m. At best, the present route formulates a "
            "superselection target."
        ),
        "next_required": [
            "derive_worldvolume_flux_quantum_normalization",
            "derive_non_circular_relation_between_flux_integer_and_chi_LL",
            "check_whether_quantization_fixes_chi_LL_or_only_chi_LL_times_Rs",
        ],
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Flux Quantization Gate",
        "",
        payload["interpretation"],
        "",
        f"Flux quantization selects chi: `{payload['flux_quantization_selects_chi']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
