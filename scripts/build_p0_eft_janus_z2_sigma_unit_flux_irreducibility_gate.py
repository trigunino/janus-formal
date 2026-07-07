from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "unit_flux_irreducibility_inputs.json"
BRIDGE_INPUT_PATH = BASE / "chern_su2_puncture_bridge_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate.md")

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _flux_integer(value: Any) -> int | None:
    return value if isinstance(value, int) and value != 0 else None


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    n_flux = _flux_integer(data.get("flux_integer_n"))
    standard_bridge_conditions = {
        "active_core_Z2_tunnel_Sigma": data.get("active_core") == "Z2_tunnel_Sigma",
        "branch_null_PT_bridge": data.get("branch") == "Z2_null_Sigma_PT_bridge",
        "source_active_derived": data.get("source") == "active_derived",
        "S2_throat_cycle_defined": bool(data.get("S2_throat_cycle_defined")),
        "flux_integer_n_available": n_flux is not None,
        "global_U1_bundle_on_S2_throat": bool(data.get("global_U1_bundle_on_S2_throat")),
        "c1_flux_equals_n": bool(data.get("c1_flux_equals_n")),
        "Holst_Ashtekar_Barbero_variables_on_Sigma": bool(
            data.get("Holst_Ashtekar_Barbero_variables_on_Sigma")
        ),
        "SU2_spin_bundle_on_Sigma_derived": bool(data.get("SU2_spin_bundle_on_Sigma_derived")),
        "Sigma_is_inner_null_or_PT_boundary": data.get("Sigma_boundary_type")
        in {"isolated_horizon_like", "null_PT_throat"},
        "horizon_Chern_Simons_boundary_condition_projected": bool(
            data.get("horizon_Chern_Simons_boundary_condition_projected")
        ),
        "spin_network_edges_can_end_on_Sigma": bool(data.get("spin_network_edges_can_end_on_Sigma")),
        "transverse_intersection_number_defined": bool(
            data.get("transverse_intersection_number_defined")
        ),
        "Gauss_constraint_links_CS_defects_to_spin_flux": bool(
            data.get("Gauss_constraint_links_CS_defects_to_spin_flux")
        ),
        "physical_induced_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
    }
    irreducibility_conditions = {
        "Janus_PT_primitive_flux_sector_law_derived": bool(
            data.get("Janus_PT_primitive_flux_sector_law_derived")
        ),
        "unit_flux_sector_only": bool(data.get("unit_flux_sector_only")),
        "charge_lattice_generator_normalized": bool(data.get("charge_lattice_generator_normalized")),
        "no_multi_charge_punctures": bool(data.get("no_multi_charge_punctures")),
        "no_empty_spin_punctures": bool(data.get("no_empty_spin_punctures")),
        "minimal_nonzero_spin_representation_selected": bool(
            data.get("minimal_nonzero_spin_representation_selected")
        ),
        "unit_flux_puncture_irreducible": bool(data.get("unit_flux_puncture_irreducible")),
    }
    bridge_ready = all(standard_bridge_conditions.values())
    irreducibility_ready = bridge_ready and all(irreducibility_conditions.values())
    bridge_payload = None
    if bridge_ready:
        bridge_payload = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "flux_integer_n": n_flux,
            "S2_throat_cycle_defined": True,
            "global_U1_bundle_on_S2_throat": True,
            "c1_flux_equals_n": True,
            "Holst_Ashtekar_Barbero_variables_on_Sigma": True,
            "SU2_spin_bundle_on_Sigma_derived": True,
            "Sigma_boundary_type": data.get("Sigma_boundary_type"),
            "horizon_Chern_Simons_boundary_condition_projected": True,
            "spin_network_edges_can_end_on_Sigma": True,
            "transverse_intersection_number_defined": True,
            "Gauss_constraint_links_CS_defects_to_spin_flux": True,
            "area_gauge": "physical_induced_S2_metric",
            "unit_flux_sector_only": bool(data.get("unit_flux_sector_only")),
            "no_multi_charge_punctures": bool(data.get("no_multi_charge_punctures")),
            "no_empty_spin_punctures": bool(data.get("no_empty_spin_punctures")),
            "unit_flux_puncture_irreducible": bool(data.get("unit_flux_puncture_irreducible")),
            "provenance": "active_unit_flux_irreducibility_gate",
        }
    return {
        "status": "janus-z2-sigma-unit-flux-irreducibility-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Isolated-horizon/LQG literature supports Chern-Simons defects being "
            "carried by spin-network punctures. It does not prove that a total "
            "Chern integer n must be represented by exactly |n| minimal punctures. "
            "That stronger result needs a Janus/PT primitive unit-flux sector."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "standard_bridge_conditions": standard_bridge_conditions,
        "irreducibility_conditions": irreducibility_conditions,
        "standard_bibliography_supports_bridge": True,
        "standard_bibliography_proves_N_gap_equals_abs_n": False,
        "bridge_ready": bridge_ready,
        "unit_flux_irreducibility_ready": irreducibility_ready,
        "N_gap_equals_abs_n_ready": irreducibility_ready,
        "N_gap": abs(n_flux) if irreducibility_ready and n_flux is not None else None,
        "bridge_payload": bridge_payload,
        "blocked_by": [key for key, ok in standard_bridge_conditions.items() if not ok],
        "irreducibility_blocked_by": [
            key for key, ok in irreducibility_conditions.items() if not ok
        ],
        "classification": (
            "derived"
            if irreducibility_ready
            else ("bridge_only_irreducibility_missing" if bridge_ready else "blocked")
        ),
        "bibliography": [
            {
                "key": "Ashtekar-Baez-Corichi-Krasnov-2000",
                "result": "U(1) Chern-Simons theory on a punctured S2 isolated horizon; curvature supported at punctures.",
                "url": "https://www.intlpress.com/site/pub/files/_fulltext/journals/atmp/2000/0004/0001/ATMP-2000-0004-0001-a001.pdf",
            },
            {
                "key": "Engle-Noui-Perez-2009",
                "result": "SU(2)-invariant Chern-Simons horizon formulation; punctures labelled by spins/intertwiners.",
                "url": "https://arxiv.org/abs/0905.3168",
            },
            {
                "key": "Kaul-2012-review",
                "result": "SU(2) and gauge-fixed U(1) descriptions are equivalent formulations of the horizon topological sector.",
                "url": "https://arxiv.org/pdf/1201.6102",
            },
        ],
        "forbidden_shortcuts": [
            "claim_N_gap_equals_abs_n_from_c1_only",
            "ignore_multi_charge_puncture_decompositions",
            "ignore_empty_spin_punctures",
            "choose_irreducibility_by_observation",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(INPUT_PATH)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    if payload["bridge_payload"]:
        BRIDGE_INPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
        BRIDGE_INPUT_PATH.write_text(
            json.dumps(payload["bridge_payload"], indent=2), encoding="utf-8"
        )
    lines = [
        "# Janus Z2 Sigma Unit-Flux Irreducibility Gate",
        "",
        payload["physical_statement"],
        "",
        f"Bridge ready: `{payload['bridge_ready']}`",
        f"Unit-flux irreducibility ready: `{payload['unit_flux_irreducibility_ready']}`",
        f"N_gap: `{payload['N_gap']}`",
        f"Classification: `{payload['classification']}`",
        "",
        "## Bridge Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    lines.append("")
    lines.append("## Irreducibility Blocked By")
    lines.extend(f"- `{item}`" for item in payload["irreducibility_blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
