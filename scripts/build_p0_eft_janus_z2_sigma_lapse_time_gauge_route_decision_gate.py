from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_lapse_slice_from_janus_gauge_probe import (
    build_payload as build_lapse_slice_probe,
)
from scripts.build_bianchi_flrw_lapse_volume_audit import (
    build_payload as build_lapse_volume_audit,
)
from scripts.build_p0_eft_janus_z2_sigma_time_gauge_leaf_action_input_writer_gate import (
    build_payload as build_leaf_action_writer,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_lapse_time_gauge_route_decision_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_lapse_time_gauge_route_decision_gate.json"
)


def build_payload() -> dict:
    lapse_slice = build_lapse_slice_probe()
    lapse_volume = build_lapse_volume_audit()
    leaf_action = build_leaf_action_writer()
    restricted_flrw_lapse_ready = bool(
        lapse_slice["proper_time_slicing_can_fix_lapse"]
        and lapse_slice["flrw_comoving_branch_can_fix_lapse_slice"]
        and lapse_volume["determinant_formula_closed"]
    )
    active_time_leaf_ready = bool(leaf_action["gate_passed"])
    return {
        "status": "janus-z2-sigma-lapse-time-gauge-route-decision-gate",
        "active_core": "Z2_tunnel_Sigma",
        "restricted_FLRW_proper_time_lapse_ready": restricted_flrw_lapse_ready,
        "active_Z2_time_leaf_action_ready": active_time_leaf_ready,
        "general_perturbed_lapse_slice_fixed": bool(
            lapse_slice["general_perturbed_branch_lapse_slice_fixed"]
        ),
        "determinant_lapse_formula_closed": bool(lapse_volume["determinant_formula_closed"]),
        "can_fix_branch_lapse_for_FLRW_background": restricted_flrw_lapse_ready,
        "can_fix_dimensional_H0": False,
        "why_H0_still_blocked": (
            "FLRW proper-time gauge can set the branch lapse convention, but it "
            "does not set the dimensional expansion scale. H0 still requires "
            "on-shell Hamiltonian constraint/surface-energy normalization."
        ),
        "source_audits": {
            "lapse_slice_probe": lapse_slice["status"],
            "lapse_volume_audit": lapse_volume["status"],
            "time_gauge_leaf_action_writer_passed": leaf_action["gate_passed"],
        },
        "forbidden_shortcuts": [
            "do_not_turn_FLRW_N_equals_1_into_numeric_H0",
            "do_not_use_quartic_lapse_volume_ratio_as_H0",
            "do_not_apply_restricted_FLRW_lapse_to_perturbed_branch",
        ],
        "next_required": [
            "derive_on_shell_Hamiltonian_constraint_value",
            "derive_boundary_surface_energy_normalization",
            "then_write_background_H0_normalization_inputs_json",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Lapse Time-Gauge Route Decision Gate",
        "",
        f"Restricted FLRW lapse ready: `{payload['restricted_FLRW_proper_time_lapse_ready']}`",
        f"Active Z2 time leaf action ready: `{payload['active_Z2_time_leaf_action_ready']}`",
        f"Can fix dimensional H0: `{payload['can_fix_dimensional_H0']}`",
        "",
        payload["why_H0_still_blocked"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
