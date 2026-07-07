from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_null_sigma_bulk_rs_to_global_mass_gate import (
    build_payload as build_bulk_rs_to_global_mass,
)
from scripts.build_p0_eft_janus_z2_null_sigma_global_noether_souriau_mass_bridge_gate import (
    build_payload as build_global_mass_to_bridge,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_tension_to_rs_gate import (
    build_payload as build_llbrane_tension_to_rs,
)
from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate import (
    build_payload as build_llbrane_tension_frontier,
)
from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import (
    build_payload as build_mass_charge_to_rs,
)


BASE = Path("outputs/active_z2_sigma")
LLBRANE_INPUT = BASE / "null_bridge_llbrane_tension_inputs.json"
BULK_RS_PATH = BASE / "null_bridge_bulk_solution_rs_inputs.json"
GLOBAL_MASS_PATH = BASE / "null_bridge_global_mass_solution_inputs.json"
MASS_CHARGE_PATH = BASE / "null_bridge_mass_charge_inputs.json"
RS_SCALE_PATH = BASE / "null_bridge_rs_scale_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_null_sigma_llbrane_bridge_chain.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_null_sigma_llbrane_bridge_chain.json")


def _first_blocker(stages: dict[str, dict[str, Any]]) -> str | None:
    for name, payload in stages.items():
        if not payload.get("gate_passed", False):
            return name
    return None


def build_payload(
    *,
    llbrane_input: Path = LLBRANE_INPUT,
    bulk_rs_path: Path = BULK_RS_PATH,
    global_mass_path: Path = GLOBAL_MASS_PATH,
    mass_charge_path: Path = MASS_CHARGE_PATH,
    rs_scale_path: Path = RS_SCALE_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    llbrane = build_llbrane_tension_to_rs(
        input_path=llbrane_input,
        output_path=bulk_rs_path,
        write_output=write_output,
    )
    bulk_mass = build_bulk_rs_to_global_mass(
        input_path=bulk_rs_path,
        output_path=global_mass_path,
        write_output=write_output,
    )
    global_bridge = build_global_mass_to_bridge(
        input_path=global_mass_path,
        output_path=mass_charge_path,
        write_output=write_output,
    )
    mass_rs = build_mass_charge_to_rs(
        input_path=mass_charge_path,
        output_path=rs_scale_path,
        write_output=write_output,
    )
    tension_frontier = build_llbrane_tension_frontier()
    stages = {
        "llbrane_tension_to_Rs": llbrane,
        "bulk_Rs_to_global_mass": bulk_mass,
        "global_mass_to_bridge_mass": global_bridge,
        "bridge_mass_to_Rs": mass_rs,
    }
    first_blocker = _first_blocker(stages)
    final_payload = mass_rs.get("rs_payload")
    return {
        "status": "janus-z2-null-sigma-llbrane-bridge-chain",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "extension_status": "explicit_LL_brane_source",
        "pipeline": [
            "chi_LL_abs_inverse_m -> R_s",
            "R_s -> M_plus=-M_minus",
            "M_plus -> M_bridge",
            "M_bridge -> R_s consistency",
        ],
        "stages": stages,
        "tension_derivation_frontier": tension_frontier,
        "first_blocker": first_blocker,
        "chain_passed": first_blocker is None,
        "final_rs_scale_payload": final_payload,
        "next_required": []
        if first_blocker is None
        else (
            tension_frontier["next_required"]
            if first_blocker == "llbrane_tension_to_Rs"
            else stages[first_blocker].get("next_required", [])
        ),
        "policy": [
            "LL-brane source is an explicit extension, not strict no-extension closure",
            "chi_LL must be derived from Janus/LL-brane dynamics or active state data",
            "no observational fit, compressed Planck/LCDM input, or archived Z4 reuse",
        ],
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Bridge Chain",
        "",
        f"Chain passed: `{payload['chain_passed']}`",
        f"First blocker: `{payload['first_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
