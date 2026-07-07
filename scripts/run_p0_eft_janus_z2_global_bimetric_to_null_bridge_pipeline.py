from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_global_bimetric_source_scale_audit_gate import (
    build_payload as build_source_audit,
)
from scripts.build_p0_eft_janus_z2_global_bimetric_stress_energy_mass_reducer_gate import (
    build_payload as build_stress_energy_mass,
)
from scripts.build_p0_eft_janus_z2_global_matter_state_from_noether_baryon_volume_gate import (
    build_payload as build_noether_matter_state,
)
from scripts.build_p0_eft_janus_z2_null_sigma_global_noether_souriau_mass_bridge_gate import (
    build_payload as build_global_to_bridge,
)
from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import (
    build_payload as build_bridge_to_rs,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_bimetric_to_null_bridge_pipeline.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_bimetric_to_null_bridge_pipeline.json"
)


def build_payload(*, write_intermediate: bool = False) -> dict:
    source_audit = build_source_audit()
    noether_matter_state = build_noether_matter_state(write_output=write_intermediate)
    stress_energy_mass = build_stress_energy_mass(write_output=write_intermediate)
    global_to_bridge = build_global_to_bridge(write_output=write_intermediate)
    bridge_to_rs = build_bridge_to_rs(write_output=write_intermediate)
    return {
        "status": "janus-z2-global-bimetric-to-null-bridge-pipeline",
        "source_audit": source_audit,
        "noether_matter_state": noether_matter_state,
        "stress_energy_mass": stress_energy_mass,
        "global_to_bridge": global_to_bridge,
        "bridge_to_rs": bridge_to_rs,
        "global_mass_state_available": global_to_bridge["global_mass_solution_available"],
        "absolute_Rs_selected": bridge_to_rs["absolute_Rs_selected"],
        "pipeline_passed": (
            global_to_bridge["global_mass_solution_available"]
            and bridge_to_rs["absolute_Rs_selected"]
        ),
        "next_required": []
        if (
            global_to_bridge["global_mass_solution_available"]
            and bridge_to_rs["absolute_Rs_selected"]
        )
        else [
            "derive_global_bimetric_stress_energy_state_or_clean_mass_state",
            "then_run_global_noether_souriau_mass_bridge",
            "then_run_mass_charge_to_Rs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload(write_intermediate=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global Bimetric To Null Bridge Pipeline",
        "",
        f"Global mass state available: `{payload['global_mass_state_available']}`",
        f"Absolute R_s selected: `{payload['absolute_Rs_selected']}`",
        f"Pipeline passed: `{payload['pipeline_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
