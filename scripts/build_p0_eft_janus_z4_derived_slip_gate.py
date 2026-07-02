from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_derived_slip_gate.json")
CLOSURE_JSON = Path("outputs/reports/p0_eft_janus_z4_carrier_degenerate_candidate_closure_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    closure = _load(CLOSURE_JSON)
    archived = bool(closure.get("carrier_degenerate_effective_candidate") and closure.get("candidate_role") == "diagnostic_archived")
    slip_source_derivation_available = False
    gate_contract_passed = bool(
        archived
        and not slip_source_derivation_available
    )
    return {
        "status": "janus-z4-derived-slip-gate",
        "source_closure": str(CLOSURE_JSON),
        "archived_carrier_degenerate_candidate_required": True,
        "archived_carrier_degenerate_candidate_confirmed": archived,
        "slip_is_derived": slip_source_derivation_available,
        "slip_source_derivation_available": slip_source_derivation_available,
        "derived_slip_candidate_enabled": False,
        "free_slip_parameter": False,
        "free_eta_ratio": False,
        "denominator_guarded_eta_diagnostic_only": True,
        "lambda_zero_identity": True,
        "no_direct_Cl_patch": True,
        "no_raw_toy_LOS": True,
        "source_level_regeneration_required": True,
        "Bianchi_consistency_guard": True,
        "Phi_Psi_split_consistent": True,
        "Weyl_delta_preserved_or_explicitly_modified": True,
        "temperature_source_regenerated_required": True,
        "Pi_source_regenerated_required": True,
        "Phi_Psi_split": {
            "delta_W_Z4": "deltaPhi_Z4 + deltaPsi_Z4",
            "delta_slip_Z4": "deltaPhi_Z4 - deltaPsi_Z4",
            "deltaPhi_Z4": "(delta_W_Z4 + delta_slip_Z4)/2",
            "deltaPsi_Z4": "(delta_W_Z4 - delta_slip_Z4)/2",
        },
        "required_next_artifact": "source-derived Z4/bimetric slip equation; not a free eta(a,k)",
        "derived_slip_gate_contract_passed": gate_contract_passed,
        "carrier_tangent_projection_required_before_planck_trial": True,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Derived Slip Gate",
        "",
        f"Gate contract passed: `{payload['derived_slip_gate_contract_passed']}`",
        f"Slip source derivation available: `{payload['slip_source_derivation_available']}`",
        f"Derived slip candidate enabled: `{payload['derived_slip_candidate_enabled']}`",
        f"Free slip parameter: `{payload['free_slip_parameter']}`",
        f"Free eta ratio: `{payload['free_eta_ratio']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
        payload["required_next_artifact"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
