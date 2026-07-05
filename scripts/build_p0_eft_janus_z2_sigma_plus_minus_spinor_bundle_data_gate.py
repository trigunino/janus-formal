from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_pin_lift_gate import (
    build_payload as build_resolved_tunnel_pin_lift_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_spinor_bundle_data_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plus_minus_spinor_bundle_data_gate.json")


def build_payload() -> dict:
    pin_lift = build_resolved_tunnel_pin_lift_payload()
    resolved_tunnel_pin_lift_ready = pin_lift["resolved_tunnel_pin_lift_ready"]
    declared = {
        "spin_Pin_bibliography_checked": True,
        "RP4_Pin_plus_result_imported": True,
        "projective_tunnel_topology_imported": True,
        "Sigma_APS_Pin_lift_input_imported": True,
        "resolved_tunnel_Pin_lift_gate_declared": True,
        "plus_sector_spinor_bundle_declared": True,
        "minus_sector_spinor_bundle_declared": True,
        "gravitational_sign_separated_from_spinor_bundle": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "resolved_tunnel_Pin_lift_ready": resolved_tunnel_pin_lift_ready,
        "plus_spinor_bundle_ready": False,
        "minus_spinor_bundle_ready": False,
        "plus_minus_spinor_bundle_data_ready": False,
    }
    return {
        "status": "janus-z2-sigma-plus-minus-spinor-bundle-data-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "spin and Pin structures via Stiefel-Whitney obstructions",
            "Pin structures on real projective spaces, including RP4 examples",
            "active projective-tunnel and Sigma APS/Pin gates",
            "active resolved tunnel Pin lift gate",
        ],
        "bibliography_result": (
            "The literature supports generic Spin/Pin bundle existence tests and "
            "the RP4 Pin+ / not Pin- pattern. It does not close the active lifted "
            "plus/minus spinor bundles on the resolved Janus tunnel."
        ),
        "source_links": [
            "https://arxiv.org/pdf/2501.01848",
            "https://trautman.fuw.edu.pl/publications/Papers-in-pdf/67.pdf",
            "https://ncatlab.org/nlab/files/Milnor-SpinStructures.pdf",
        ],
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "resolved_tunnel_pin_lift": {
                "gate": pin_lift["status"],
                "ready": pin_lift["resolved_tunnel_pin_lift_ready"],
                "closure": pin_lift["closure"],
            },
        },
        "nearest_spinor_bundle_frontier": {
            "block": "resolved_tunnel_Pin_lift",
            "gate": "P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate",
            "diagnostic_only": True,
        },
        "formulas": {
            "pin_input": "RP4 base: Pin+ imported; Sigma APS/Pin lift remains active input",
            "plus_bundle": "S_+ -> M_+ declared over resolved tunnel sheet",
            "minus_bundle": "S_- -> M_- declared over resolved tunnel sheet",
            "sign_policy": "negative gravitational sign is not a negative spinor-bundle norm",
        },
        "plus_minus_spinor_bundle_data_ledger_declared": all(declared.values()),
        "plus_minus_spinor_bundle_data_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "close_resolved_tunnel_Pin_lift",
            "pass_resolved_tunnel_Pin_lift_gate",
            "derive_plus_sector_spinor_bundle",
            "derive_minus_sector_spinor_bundle",
            "feed_plus_minus_bundles_to_spinor_projection_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Plus/Minus Spinor Bundle Data Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['plus_minus_spinor_bundle_data_ledger_declared']}`",
        f"Bundle data ready: `{payload['plus_minus_spinor_bundle_data_ready']}`",
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
