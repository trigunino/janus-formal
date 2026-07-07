from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_relation_audit_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_relation_audit_gate.json"
)


def build_payload() -> dict:
    closure = {
        "worldvolume_topology_declared": True,
        "natural_LL_flux_cycle_identified": True,
        "integer_flux_law_formulated": True,
        "on_shell_F2_constant_declared": True,
        "conditional_Rs_from_flux_formula_available": True,
        "worldvolume_charge_normalization_derived": False,
        "auxiliary_metric_to_physical_area_gauge_fixed": False,
        "F2_constant_from_Janus_action_derived": False,
        "non_circular_chi_LL_value_derived": False,
    }
    return {
        "status": "janus-z2-null-sigma-llbrane-flux-quantization-relation-audit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "extension_status": "explicit_LL_brane_source_frontier",
        "topology": {
            "worldvolume": "null generator x S2_throat",
            "natural_flux_cycle": "S2_throat",
            "aroundSigma_Z2_cycle_role": (
                "geometric deck/transport cycle, not by itself the LL gauge flux "
                "cycle unless a pullback map from the worldvolume gauge bundle is derived"
            ),
        },
        "conditional_flux_algebra": {
            "flux_law": "integral_{S2} F_LL = 2*pi*n/q_LL",
            "SO3_ansatz": "F_theta_phi = B*sin(theta)",
            "B_from_flux": "B = n/(2*q_LL)",
            "on_shell_constraint": "F2 = F2_0 from the LL worldvolume L(F2) sector",
            "conditional_scale": (
                "with an induced-area gauge, R_s^2 is proportional to "
                "|n|/(q_LL*sqrt(F2_0))"
            ),
            "chi_relation": "chi_LL = -1/(8*pi*R_s) after ER/LL matching",
        },
        "closure": closure,
        "flux_relation_closes_chi": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "interpretation": (
            "Flux quantization gives a real superselection target. It can only fix "
            "R_s or chi_LL after three extra non-observational inputs are derived: "
            "the worldvolume charge quantum q_LL, the auxiliary-metric/physical-area "
            "gauge, and the Janus on-shell value F2_0. Without these, the flux law "
            "quantizes a formal charge but does not select an absolute tension."
        ),
        "next_required": [
            "derive_worldvolume_charge_quantum_q_LL",
            "derive_auxiliary_metric_to_physical_area_gauge_on_Sigma",
            "derive_F2_0_from_the_Janus_LLbrane_worldvolume_action",
            "then_test_whether_Rs_or_only_chiLL_times_Rs_is_quantized",
        ],
        "forbidden_shortcuts": [
            "do_not_use_aroundSigma_Z2_cycle_as_LL_flux_cycle_without_bundle_pullback",
            "do_not_set_q_LL_or_F2_0_by_observation",
            "do_not_claim_flux_quantization_fixes_chi_before_auxiliary_metric_gauge",
        ],
        "gate_passed": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane Flux Quantization Relation Audit Gate",
        "",
        payload["interpretation"],
        "",
        f"Flux relation closes chi: `{payload['flux_relation_closes_chi']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
