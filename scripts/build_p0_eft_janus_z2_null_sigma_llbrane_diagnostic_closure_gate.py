from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate import (
    build_payload as build_tension_frontier,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_llbrane_diagnostic_closure_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_null_sigma_llbrane_diagnostic_closure_gate.json"
)


def build_payload() -> dict:
    frontier = build_tension_frontier()
    return {
        "status": "janus-z2-null-sigma-llbrane-diagnostic-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "diagnostic_closure_decision": "close_as_viable_state_parameter_extension",
        "strict_no_extension_status": "blocked",
        "LL_brane_extension_status": "viable_but_chi_LL_state_parameter",
        "closed_results": [
            "null/PT geometry reduced",
            "LL-brane source consistency available",
            "m = 1/(16*pi*abs(chi_LL))",
            "R_s = 1/(8*pi*abs(chi_LL))",
            "M_minus = -M_plus",
            "PT boundary state fixes sign/pairing/constancy only",
            "flux quantization target formulated but not closed",
        ],
        "open_blocker": "chi_LL_abs_inverse_m_not_derived",
        "tension_frontier": frontier,
        "allowed_future_reopen_conditions": [
            "derive_chi_LL_from_global_bimetric_state",
            "derive_chi_LL_from_worldvolume_flux_quantization_with_q_LL_and_F2_0",
            "accept_chi_LL_as_explicit_extension_state_input",
        ],
        "forbidden_claims": [
            "do_not_claim_no_fit_prediction",
            "do_not_claim_strict_no_extension_closure",
            "do_not_choose_chi_LL_by_observation",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Diagnostic Closure Gate",
        "",
        f"Diagnostic closure decision: `{payload['diagnostic_closure_decision']}`",
        f"Strict no-extension status: `{payload['strict_no_extension_status']}`",
        f"LL-brane extension status: `{payload['LL_brane_extension_status']}`",
        f"Open blocker: `{payload['open_blocker']}`",
        "",
        "## Closed Results",
    ]
    lines.extend(f"- `{item}`" for item in payload["closed_results"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
