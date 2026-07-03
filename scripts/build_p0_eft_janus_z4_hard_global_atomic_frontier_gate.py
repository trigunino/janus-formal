from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_hard_global_atomic_frontier_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_hard_global_atomic_frontier_gate.json")


def build_payload() -> dict:
    aps_frontier = {
        "pin_minus_lift_constructed": False,
        "aps_fredholm_domain_constructed": False,
        "pt_spectral_eta_cancellation_constructed": False,
        "parity_anomaly_cancelled": False,
        "trace_regularization_constructed": False,
    }
    orbifold_frontier = {
        "integer_flux_theorem_closed": False,
        "branch_indices_computed": False,
        "euler_cover_data_closed": False,
        "volume_ratio_two_to_one_derived": False,
        "uniqueness_of_two_to_one_ratio": False,
    }
    aps_closed = all(aps_frontier.values())
    orbifold_closed = all(orbifold_frontier.values())
    transport_maps = {
        "aps_pt_chain_to_frontier_transport_theorem": True,
        "aps_boundary_geometry_chain_to_frontier_transport_theorem": True,
        "orbifold_flux_chain_to_frontier_transport_theorem": True,
        "orbifold_integer_flux_orientation_chain_to_frontier_transport_theorem": True,
        "aps_frontier_to_refined_gate_transport_theorem": True,
        "orbifold_frontier_to_refined_gate_transport_theorem": True,
        "frontier_items_still_require_direct_proofs": True,
    }
    closure_policy = {
        "aps_direct_witness_required": True,
        "orbifold_direct_witness_required": True,
        "synthetic_true_closure_forbidden": True,
        "imported_theorem_must_match_target": True,
        "no_fit_promotion_requires_closed_frontier": True,
    }
    return {
        "status": "janus-z4-hard-global-atomic-frontier-gate",
        "lean_module": "P0EFTJanusZ4HardGlobalAtomicFrontierGate",
        "aps_frontier": aps_frontier,
        "orbifold_frontier": orbifold_frontier,
        "transport_maps": transport_maps,
        "closure_policy": closure_policy,
        "aps_frontier_closed": aps_closed,
        "orbifold_frontier_closed": orbifold_closed,
        "aps_refined_gate_can_close": aps_closed,
        "orbifold_refined_gate_can_close": orbifold_closed,
        "pure_math_model_closed_without_axioms": aps_closed and orbifold_closed,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required_gate": "prove_frontier_items_or_import_matching_theorems",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Hard Global Atomic Frontier Gate",
        "",
        f"APS frontier closed: `{payload['aps_frontier_closed']}`",
        f"Orbifold frontier closed: `{payload['orbifold_frontier_closed']}`",
        f"APS PT chain transport theorem: `{payload['transport_maps']['aps_pt_chain_to_frontier_transport_theorem']}`",
        f"APS boundary geometry chain transport theorem: `{payload['transport_maps']['aps_boundary_geometry_chain_to_frontier_transport_theorem']}`",
        f"Orbifold flux chain transport theorem: `{payload['transport_maps']['orbifold_flux_chain_to_frontier_transport_theorem']}`",
        f"Orbifold integer-flux/orientation chain theorem: `{payload['transport_maps']['orbifold_integer_flux_orientation_chain_to_frontier_transport_theorem']}`",
        f"APS frontier transport theorem: `{payload['transport_maps']['aps_frontier_to_refined_gate_transport_theorem']}`",
        f"Orbifold frontier transport theorem: `{payload['transport_maps']['orbifold_frontier_to_refined_gate_transport_theorem']}`",
        f"Synthetic True closure forbidden: `{payload['closure_policy']['synthetic_true_closure_forbidden']}`",
        f"Imported theorem must match target: `{payload['closure_policy']['imported_theorem_must_match_target']}`",
        "",
        "## APS frontier",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["aps_frontier"].items())
    lines.extend(["", "## Orbifold frontier"])
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in payload["orbifold_frontier"].items()
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
