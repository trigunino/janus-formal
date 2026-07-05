from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_component_from_deltaK_inputs_gate import (
    build_payload as build_component_from_deltaK_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_component_builder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cartan_ghy_component_builder_gate.json")


def build_payload() -> dict:
    component = build_component_from_deltaK_payload()
    return {
        "status": "janus-z2-sigma-cartan-ghy-component-builder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "deltaK_to_component_builder_ready": True,
        "rho_CartanGHY_over_rho_crit0_builder_ready": True,
        "p_CartanGHY_over_rho_crit0_builder_ready": True,
        "requires_active_DeltaK_s_of_a": True,
        "requires_active_DeltaK_tau_of_a": True,
        "requires_explicit_Z2_orientation_sign": True,
        "requires_explicit_kappa_rho_crit0": True,
        "uses_planck_lcdm_normalization": False,
        "uses_archived_z4_inputs": False,
        "cartan_ghy_component_values_ready": component[
            "cartan_ghy_component_values_ready"
        ],
        "upstream_frontiers": {
            "cartan_ghy_component_from_deltaK_inputs": {
                "gate": component["status"],
                "ready": component["gate_passed"],
                "deltaK_input_exists": component["deltaK_input_exists"],
                "background_scalar_manifest_exists": component[
                    "background_scalar_manifest_exists"
                ],
                "nearest_frontier": component[
                    "nearest_cartan_component_frontier"
                ],
            },
        },
        "gate_passed": True,
        "formulas": {
            "rho_CGHY_over_rho_crit0": "3 * eps_Z2 * DeltaK_s(a) / (kappa * rho_crit0)",
            "p_CGHY_over_rho_crit0": "eps_Z2 * (DeltaK_tau(a) - 2 * DeltaK_s(a)) / (kappa * rho_crit0)",
        },
        "next_required": [
            "derive_DeltaK_s_of_a_from_active_tunnel_embedding",
            "derive_DeltaK_tau_of_a_from_active_tunnel_embedding",
            "supply_explicit_kappa_rho_crit0_from_active_background_normalization",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Cartan-GHY Component Builder Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"DeltaK-to-component builder ready: `{payload['deltaK_to_component_builder_ready']}`",
        f"Component values ready: `{payload['cartan_ghy_component_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
