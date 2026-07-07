from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_s2_flux_topology_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_null_sigma_llbrane_s2_flux_topology_gate.json"
)


def build_payload() -> dict:
    topology = {
        "worldvolume_topology": "R_null_generator x S2_throat",
        "flux_cycle": "S2_throat",
        "H2_S2_Z": "Z",
        "first_Chern_class_available": True,
        "integer_flux_sector_available": True,
        "integer_label": "n in Z",
    }
    closure = {
        "S2_throat_cycle_defined": True,
        "H2_supports_integer_flux": True,
        "U1_bundle_quantization_law_available": True,
        "n_can_label_superselection_sector": True,
        "q_LL_normalization_derived": False,
        "F2_0_derived": False,
        "physical_area_gauge_derived": False,
        "chi_LL_numeric_derived": False,
    }
    return {
        "status": "janus-z2-null-sigma-llbrane-s2-flux-topology-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "topology": topology,
        "flux_quantization_statement": (
            "For a global U(1) LL worldvolume gauge bundle on S2_throat, "
            "the flux sector is labelled by c1 = n in H2(S2,Z), with "
            "integral_S2 F_LL = 2*pi*n/q_LL after charge normalization."
        ),
        "closure": closure,
        "topology_gate_passed": True,
        "chi_selection_gate_passed": False,
        "next_required": [
            "derive_worldvolume_charge_quantum_q_LL",
            "derive_F2_0_from_specific_L_of_F2",
            "derive_physical_induced_S2_area_gauge",
        ],
        "forbidden_shortcuts": [
            "do_not_set_n_by_observation",
            "do_not_absorb_q_LL_into_n_after_declaring_integer_flux",
            "do_not_claim_topology_alone_fixes_chi_LL",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Null Sigma LL-Brane S2 Flux Topology Gate",
        "",
        payload["flux_quantization_statement"],
        "",
        f"Topology gate passed: `{payload['topology_gate_passed']}`",
        f"Chi selection gate passed: `{payload['chi_selection_gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
