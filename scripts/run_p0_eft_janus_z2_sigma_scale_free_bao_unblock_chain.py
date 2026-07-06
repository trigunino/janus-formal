from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_bao_active_primitive_physical_input_obligation_gate import (
    build_payload as build_primitive_obligation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_to_scale_free_primitive_chi2_gate import (
    build_payload as build_component_to_chi2_payload,
)
from scripts.run_p0_eft_janus_z2_sigma_plasma_unblock_chain import (
    build_payload as build_plasma_chain_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_scale_free_bao_unblock_chain.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_scale_free_bao_unblock_chain.json")


def build_payload() -> dict:
    plasma = build_plasma_chain_payload()
    primitive_obligations = build_primitive_obligation_payload()
    primitive_chain = build_component_to_chi2_payload()
    passed = bool(
        plasma["chain_passed"]
        and primitive_obligations["gate_passed"]
        and primitive_chain["gate_passed"]
    )
    if passed:
        blocker = "none"
    elif not plasma["chain_passed"]:
        blocker = plasma["primary_blocker"]
    elif not primitive_obligations["gate_passed"]:
        blocker = primitive_obligations["blocker"]
    else:
        blocker = primitive_chain["blocker"]
    return {
        "status": "janus-z2-sigma-scale-free-bao-unblock-chain",
        "active_core": "Z2_tunnel_Sigma",
        "plasma_chain": plasma,
        "primitive_obligations": primitive_obligations,
        "primitive_chi2_chain": primitive_chain,
        "bao_chi2_evaluated": primitive_chain.get("bao_chi2_evaluated", False),
        "chi2_DESI_DR2_BAO": primitive_chain.get("chi2_DESI_DR2_BAO"),
        "chain_passed": passed,
        "full_no_fit_prediction_ready": False,
        "primary_blocker": blocker,
        "next_required": [
            "derive_or_supply_projected_occupation_state_inputs_json",
            "derive_H0_Z2Sigma_or_R_curv_Z2Sigma_m",
            "derive_or_supply_flrw_component_inputs_json",
            "then_run_component_to_scale_free_primitive_chi2",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Scale-Free BAO Unblock Chain",
                "",
                f"Plasma chain passed: `{payload['plasma_chain']['chain_passed']}`",
                f"Primitive obligations passed: `{payload['primitive_obligations']['gate_passed']}`",
                f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
                f"Chain passed: `{payload['chain_passed']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
                "",
                "## Next Required",
                *[f"- `{item}`" for item in payload["next_required"]],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
