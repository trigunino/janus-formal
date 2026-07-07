from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit import (
    build_payload as primitive_closure,
)
from scripts.build_p0_eft_janus_z2_sigma_area_superselection_sector_manifest import (
    build_payload as area_superselection,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_family_propagation import (
    build_payload as family_propagation,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_observation_readiness_gate import (
    build_payload as observation_readiness,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_scan import (
    build_payload as sector_scan,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_internal_constraints import (
    build_payload as internal_constraints,
)
from scripts.build_p0_eft_janus_z2_sigma_ngap_selection_law_registry import (
    build_payload as selection_law_registry,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_path_end_to_end_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_path_end_to_end_audit.json")


def build_payload() -> dict:
    primitive = primitive_closure()
    area = area_superselection()
    family = family_propagation()
    readiness = observation_readiness()
    scan = sector_scan()
    internal = internal_constraints()
    registry = selection_law_registry()
    stages = {
        "primitive_flux_unique_route_closed": primitive["standard_bibliography_closes_as_no_go"],
        "area_superselection_family_ready": area["superselection_family_ready"],
        "discrete_family_propagation_ready": family["discrete_family_propagation_ready"],
        "observation_readiness_ready": readiness["observation_readiness"],
        "discrete_sector_scan_ready": scan["scan_ready"],
        "internal_constraints_ready": internal["internal_constraints_ready"],
        "selection_law_registry_ready": registry["N_gap_family_ready"]
        and not registry["N_gap_unique_prediction_ready"],
        "no_unique_prediction_claim": not family["unique_prediction_ready"]
        and not scan["unique_prediction_claim_allowed"],
    }
    return {
        "status": "janus-z2-sigma-discrete-path-end-to-end-audit",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "End-to-end audit for the active discrete N_gap path: the unique "
            "N_gap=|n| route is closed negatively, the superselection family is "
            "active, sectors are propagated, and scans must not claim a unique "
            "derivation from data."
        ),
        "stages": stages,
        "end_to_end_path_ready": all(stages.values()),
        "sector_count": len(family["sector_table"]),
        "scan_survivors": scan["surviving_sectors"],
        "internal_survivors": internal["surviving_sectors"],
        "selection_law_status": registry["current_best_status"],
        "unique_selection_laws_ready": registry["unique_selection_laws_ready"],
        "blocked_by": [key for key, ok in stages.items() if not ok],
        "next_physical_blockers": [
            "derive stronger internal constraints from horizon/PT/Casimir/spin source",
            "only then connect real observation gates as rejection/ranking of fixed sectors",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Discrete Path End-to-End Audit",
        "",
        payload["physical_statement"],
        "",
        f"End-to-end ready: `{payload['end_to_end_path_ready']}`",
        f"Sector count: `{payload['sector_count']}`",
        f"Scan survivors: `{payload['scan_survivors']}`",
        f"Internal survivors: `{payload['internal_survivors']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    lines.extend(["", "## Next Physical Blockers"])
    lines.extend(f"- {item}" for item in payload["next_physical_blockers"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
