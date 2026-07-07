from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "primitive_flux_sector_law_inputs.json"
IRREDUCIBILITY_OUTPUT = BASE / "unit_flux_irreducibility_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_primitive_flux_sector_law_investigation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_primitive_flux_sector_law_investigation.json")

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _flux_integer(value: Any) -> int | None:
    return value if isinstance(value, int) and value != 0 else None


def build_payload(
    input_path: Path = INPUT_PATH,
    irreducibility_output: Path = IRREDUCIBILITY_OUTPUT,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    n_flux = _flux_integer(data.get("flux_integer_n"))
    prerequisites = {
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
        "Sigma_boundary_type_allowed": data.get("Sigma_boundary_type")
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
    primitive_law_conditions = {
        "Janus_PT_boundary_state_selects_primitive_charge": bool(
            data.get("Janus_PT_boundary_state_selects_primitive_charge")
        ),
        "charge_lattice_generator_normalized": bool(data.get("charge_lattice_generator_normalized")),
        "fusion_of_unit_fluxes_forbidden_by_superselection": bool(
            data.get("fusion_of_unit_fluxes_forbidden_by_superselection")
        ),
        "splitting_of_unit_flux_forbidden_by_integrality": bool(
            data.get("splitting_of_unit_flux_forbidden_by_integrality")
        ),
        "empty_spin_punctures_forbidden_by_area_operator_kernel": bool(
            data.get("empty_spin_punctures_forbidden_by_area_operator_kernel")
        ),
        "minimal_nonzero_spin_representation_selected": bool(
            data.get("minimal_nonzero_spin_representation_selected")
        ),
    }
    prerequisites_ready = all(prerequisites.values())
    primitive_law_ready = prerequisites_ready and all(primitive_law_conditions.values())
    irreducibility_payload = None
    if primitive_law_ready:
        irreducibility_payload = {
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
            "Janus_PT_primitive_flux_sector_law_derived": True,
            "unit_flux_sector_only": True,
            "charge_lattice_generator_normalized": True,
            "no_multi_charge_punctures": True,
            "no_empty_spin_punctures": True,
            "minimal_nonzero_spin_representation_selected": True,
            "unit_flux_puncture_irreducible": True,
            "provenance": "active_Janus_PT_primitive_flux_sector_law",
        }
        if write_output:
            irreducibility_output.parent.mkdir(parents=True, exist_ok=True)
            irreducibility_output.write_text(
                json.dumps(irreducibility_payload, indent=2), encoding="utf-8"
            )
    return {
        "status": "janus-z2-sigma-primitive-flux-sector-law-investigation",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "This investigates whether Janus/PT itself supplies a primitive "
            "unit-flux law. Without that law, N_gap=|n| remains stronger than "
            "the standard isolated-horizon Chern-Simons puncture result."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "prerequisites": prerequisites,
        "primitive_law_conditions": primitive_law_conditions,
        "prerequisites_ready": prerequisites_ready,
        "primitive_flux_sector_law_ready": primitive_law_ready,
        "N_gap_equals_abs_n_route_open": primitive_law_ready,
        "irreducibility_payload": irreducibility_payload,
        "blocked_by": [key for key, ok in prerequisites.items() if not ok],
        "primitive_law_blocked_by": [
            key for key, ok in primitive_law_conditions.items() if not ok
        ],
        "classification": (
            "derived"
            if primitive_law_ready
            else ("bridge_ready_law_missing" if prerequisites_ready else "blocked")
        ),
        "forbidden_shortcuts": [
            "assume_primitive_sector_from_c1_only",
            "forbid_multi_charge_punctures_without_boundary_state_law",
            "choose_primitive_law_by_observation",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Primitive Flux Sector Law Investigation",
        "",
        payload["physical_statement"],
        "",
        f"Prerequisites ready: `{payload['prerequisites_ready']}`",
        f"Primitive law ready: `{payload['primitive_flux_sector_law_ready']}`",
        f"Classification: `{payload['classification']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    lines.append("")
    lines.append("## Primitive Law Blocked By")
    lines.extend(f"- `{item}`" for item in payload["primitive_law_blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
