from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_nocc_boundary_state_selection_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_nocc_boundary_state_selection_gate.json"
)


def build_payload() -> dict:
    closure = {
        "projected_Noether_charge_reduction_declared": True,
        "Q_Sigma_equals_N_occ": True,
        "charge_conservation_selects_unique_N_occ": False,
        "spinor_boundary_state_selection_law_available": False,
        "effective_initial_state_manifest_available": False,
        "N_occ_numeric_ready": False,
    }
    return {
        "status": "janus-z2-sigma-nocc-boundary-state-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "projected_Noether_charge_boundary_state_selection",
        "selection_rule": (
            "N_occ is not a surface density. It is the occupation/state label "
            "left after Q_Sigma=N_occ. It needs either a derived spinor boundary "
            "state-selection law or an explicit effective initial-state manifest."
        ),
        "closure": closure,
        "ready_for_projected_occupation_state_inputs": bool(
            closure["spinor_boundary_state_selection_law_available"]
            or closure["effective_initial_state_manifest_available"]
        ),
        "forbidden_shortcuts": [
            "do_not_convert_global_Noether_charge_to_local_density_directly",
            "do_not_fit_N_occ_to_BAO_or_CMB",
            "do_not_use_example_projected_occupation_as_active_input",
        ],
        "next_required": [
            "derive_spinor_boundary_state_selection_law",
            "or_write_explicit_projected_occupation_state_inputs_as_effective_initial_data",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma N_occ Boundary State Selection Gate",
        "",
        payload["selection_rule"],
        "",
        f"Ready for occupation input: `{payload['ready_for_projected_occupation_state_inputs']}`",
        "",
        "## Closure",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closure"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
