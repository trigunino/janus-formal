from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_area_occupation_selection_gate import (
    build_payload as area_occupation,
)
from scripts.build_p0_eft_janus_z2_sigma_area_superselection_sector_manifest import (
    build_payload as area_superselection,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_internal_constraints import (
    build_payload as internal_constraints,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_observation_trial import (
    build_payload as observation_trial,
)
from scripts.build_p0_eft_janus_z2_sigma_observation_data_inventory import (
    build_payload as data_inventory,
)
from scripts.build_p0_eft_janus_z2_sigma_ngap_to_background_source_frontier import (
    build_payload as background_frontier,
)
from scripts.build_p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit import (
    build_payload as primitive_flux_closure,
)
from scripts.build_p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate import (
    build_payload as casimir,
)
from scripts.build_p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate import (
    build_payload as horizon,
)
from scripts.build_p0_eft_janus_z2_null_sigma_chi_ll_noether_souriau_superselection_gate import (
    build_payload as souriau,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_ngap_selection_law_registry.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_ngap_selection_law_registry.json")


def build_payload() -> dict:
    occupation = area_occupation()
    superselection = area_superselection()
    internal = internal_constraints()
    obs = observation_trial()
    inventory = data_inventory()
    background = background_frontier()
    primitive = primitive_flux_closure()
    cas = casimir()
    hor = horizon()
    noether = souriau()
    laws = {
        "primitive_flux_unit_law": {
            "kind": "unique_selector_candidate",
            "non_rustine_standard": True,
            "ready": False,
            "status": "closed_negative_on_standard_bibliography",
            "reason": "c1=n does not force exactly |n| irreducible punctures",
        },
        "area_occupation_selector": {
            "kind": "unique_selector_or_superselection",
            "non_rustine_standard": True,
            "ready": occupation["occupation_selector_ready"],
            "selects_unique_N_gap": occupation["N_gap_is_unique_prediction"],
            "N_gap": occupation["N_gap"],
            "blocked_by": occupation["blocked_by"],
        },
        "active_superselection_family": {
            "kind": "discrete_family_not_unique_selector",
            "non_rustine_standard": True,
            "ready": superselection["superselection_family_ready"],
            "selects_unique_N_gap": False,
            "sector_count": len(superselection["sector_table"]),
        },
        "internal_spectral_horizon_ranking": {
            "kind": "diagnostic_ranking_not_selector",
            "non_rustine_standard": True,
            "ready": internal["internal_constraints_ready"],
            "selects_unique_N_gap": internal["internal_unique_sector_selected"],
            "survivors": internal["surviving_sectors"],
            "rankings_are_constraints": internal["diagnostic_rankings_are_constraints"],
        },
        "casimir_topological_law": {
            "kind": "frontier_selector_candidate",
            "non_rustine_standard": True,
            "ready": cas["casimir_exit_prediction_ready"],
            "blocked_by": cas.get("blockers", cas.get("next_required", [])),
        },
        "horizon_PT_first_law": {
            "kind": "frontier_selector_candidate",
            "non_rustine_standard": True,
            "ready": hor["horizon_thermodynamic_exit_ready"],
            "blocked_by": hor.get("blockers", hor.get("next_required", [])),
        },
        "noether_souriau_state_law": {
            "kind": "superselection_charge_candidate",
            "non_rustine_standard": True,
            "ready": noether["souriau_superselection_selects_chi_LL_now"],
            "selects_unique_N_gap": False,
            "blocked_by": noether["next_required"],
        },
        "observation_trial": {
            "kind": "external_rejection_or_ranking_not_internal_law",
            "non_rustine_standard": True,
            "ready": obs["trial_ready"],
            "selects_unique_N_gap": False,
            "blocked_by": obs["blocked_by"],
            "reusable_raw_datasets": inventory["reusable_raw_datasets"],
            "N_gap_to_background_source_ready": background["N_gap_to_background_source_ready"],
        },
    }
    unique_ready = [
        name
        for name, law in laws.items()
        if law.get("ready") and law.get("selects_unique_N_gap")
    ]
    family_ready = [
        name
        for name, law in laws.items()
        if law.get("ready") and law["kind"] == "discrete_family_not_unique_selector"
    ]
    return {
        "status": "janus-z2-sigma-ngap-selection-law-registry",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Registry of admissible non-rustine N_gap laws. A law may select a "
            "unique sector only if it is derived from topology/geometry/action/"
            "state data before observation. Diagnostic rankings and observations "
            "may rank or reject sectors but cannot become selection laws."
        ),
        "primitive_flux_standard_no_go": primitive["standard_bibliography_closes_as_no_go"],
        "laws": laws,
        "unique_selection_laws_ready": unique_ready,
        "superselection_family_laws_ready": family_ready,
        "current_best_status": "discrete_superselection_family",
        "N_gap_unique_prediction_ready": bool(unique_ready),
        "N_gap_family_ready": bool(family_ready),
        "forbidden_shortcuts": [
            "choose_N_gap_by_observation",
            "promote_internal_ranking_to_selection_law",
            "set_N_gap_to_minimal_value_without_ground_state_proof",
            "reuse_legacy_Z4_monodromy_without_Pin_lift_theorem",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma N_gap Selection Law Registry",
        "",
        payload["physical_statement"],
        "",
        f"Unique prediction ready: `{payload['N_gap_unique_prediction_ready']}`",
        f"Family ready: `{payload['N_gap_family_ready']}`",
        f"Current best status: `{payload['current_best_status']}`",
        "",
        "## Laws",
    ]
    for name, law in payload["laws"].items():
        lines.append(f"- `{name}`: kind=`{law['kind']}`, ready=`{law['ready']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
