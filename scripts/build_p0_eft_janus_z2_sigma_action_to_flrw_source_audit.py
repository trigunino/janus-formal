from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate import (
    build_payload as casimir,
)
from scripts.build_p0_eft_janus_z2_chi_ll_horizon_thermodynamic_exit_gate import (
    build_payload as horizon,
)
from scripts.build_p0_eft_janus_z2_cover_master_llbrane_action_extension_gate import (
    build_payload as llbrane_extension,
)


BASE = Path("outputs/active_z2_sigma")
FLRW_PATH = BASE / "flrw_components.json"
PT67_BOUNDARY_PATH = BASE / "boundary_projection_charge_from_pt67_theta.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_action_to_flrw_source_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_action_to_flrw_source_audit.json")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_zero(values: Any) -> bool:
    if not isinstance(values, list):
        return False
    return all(abs(float(value)) == 0.0 for value in values)


def _flrw_terms(flrw: dict[str, Any]) -> dict[str, Any]:
    components = flrw.get("flrw_components_over_rho_crit0", {})
    provenance = flrw.get("component_provenance", {})
    names = [
        "cartan_ghy",
        "holst_nieh_yan",
        "matter_flux",
        "counterterm",
    ]
    terms = {}
    for name in names:
        rho_key = f"{name}_rho"
        p_key = f"{name}_p"
        rho_zero = _all_zero(components.get(rho_key))
        p_zero = _all_zero(components.get(p_key))
        terms[name] = {
            "admitted_in_current_action": True,
            "variation_channel": "FLRW_stress_component",
            "rho_values": components.get(rho_key),
            "p_values": components.get(p_key),
            "rho_zero": rho_zero,
            "p_zero": p_zero,
            "emits_homogeneous_source": not (rho_zero and p_zero),
            "depends_on_N_gap": False,
            "provenance": provenance.get(rho_key),
        }
    return terms


def _pt67_boundary_term(boundary: dict[str, Any]) -> dict[str, Any]:
    q_values = boundary.get("Q_boundary_minus_reference_unit")
    q_zero = _all_zero(q_values)
    return {
        "admitted_in_current_action": True,
        "variation_channel": "Hamiltonian_boundary_charge",
        "Q_boundary_minus_reference_unit": q_values,
        "Q_ren_unit_all_zero": bool(boundary.get("Q_ren_unit_all_zero")) and q_zero,
        "projected_positive_Friedmann_source_available": bool(
            boundary.get("projected_positive_Friedmann_source_available")
        ),
        "emits_homogeneous_source": bool(
            boundary.get("projected_positive_Friedmann_source_available")
        ),
        "depends_on_N_gap": False,
        "provenance": boundary.get("interpretation"),
    }


def build_payload() -> dict[str, Any]:
    flrw = _read(FLRW_PATH)
    boundary = _read(PT67_BOUNDARY_PATH)
    cas = casimir()
    hor = horizon()
    ll = llbrane_extension()
    admitted_terms = {
        **_flrw_terms(flrw),
        "pt67_brown_york_boundary": _pt67_boundary_term(boundary),
    }
    extension_terms = {
        "casimir_topological": {
            "admitted_in_current_action": False,
            "frontier_ready": cas["casimir_exit_prediction_ready"],
            "emits_homogeneous_source_if_admitted": cas["casimir_exit_prediction_ready"],
            "blocked_by": cas["blocked_by"],
        },
        "horizon_PT_first_law": {
            "admitted_in_current_action": False,
            "frontier_ready": hor["horizon_thermodynamic_exit_ready"],
            "emits_homogeneous_source_if_admitted": hor["horizon_thermodynamic_exit_ready"],
            "blocked_by": hor["blocked_by"],
        },
        "LL_brane_null_source": {
            "admitted_in_current_action": False,
            "frontier_ready": ll["master_LLbrane_extension_ready"],
            "emits_homogeneous_source_if_admitted": False,
            "blocked_by": ll["blocked_by"],
            "reason": "coherent explicit null source extension, but chi_LL magnitude and homogeneous FLRW projection are not derived",
        },
    }
    emitting_admitted = [
        name for name, term in admitted_terms.items() if term["emits_homogeneous_source"]
    ]
    admitted_all_zero = not emitting_admitted
    return {
        "status": "janus-z2-sigma-action-to-flrw-source-audit",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Audits the currently admitted Janus/Z2/Sigma action terms by their "
            "variation with respect to the homogeneous FLRW background. It does "
            "not choose a new source channel."
        ),
        "input_manifests": {
            "flrw_components": str(FLRW_PATH),
            "pt67_boundary_projection": str(PT67_BOUNDARY_PATH),
        },
        "admitted_terms": admitted_terms,
        "extension_frontiers": extension_terms,
        "emitting_admitted_terms": emitting_admitted,
        "rho_Sigma_status": (
            "derived_zero_under_current_admitted_action"
            if admitted_all_zero
            else "nonzero_source_emitted_by_admitted_action"
        ),
        "rho_Sigma_a_derived": admitted_all_zero,
        "rho_Sigma_a_values_over_rho_crit0": [0.0, 0.0, 0.0] if admitted_all_zero else None,
        "N_gap_enters_rho_Sigma": False,
        "E_Z2Sigma_a2_ready": False,
        "sector_to_observable_map_ready": False,
        "nonzero_background_source_requires_extension": admitted_all_zero,
        "allowed_nonzero_routes": [
            "derive Casimir/topological source from field content and boundary conditions",
            "derive horizon/PT first-law source with fixed kappa_l and area law",
            "admit LL-brane null source extension and derive chi_LL plus FLRW projection",
            "derive global Noether/Souriau state charge and volume projection",
        ],
        "forbidden_shortcuts": [
            "treat throat mass as homogeneous density without volume/projection map",
            "reuse Holst/Z4/CAMB background as active Z2/Sigma source",
            "set rho_Sigma by observation",
            "promote extension frontier to admitted action without explicit decision",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Action To FLRW Source Audit",
        "",
        payload["physical_statement"],
        "",
        f"rho_Sigma status: `{payload['rho_Sigma_status']}`",
        f"E_Z2Sigma(a)^2 ready: `{payload['E_Z2Sigma_a2_ready']}`",
        f"Nonzero source requires extension: `{payload['nonzero_background_source_requires_extension']}`",
        "",
        "## Admitted Terms",
    ]
    for name, term in payload["admitted_terms"].items():
        lines.append(f"- `{name}`: emits_source=`{term['emits_homogeneous_source']}`")
    lines.extend(["", "## Extension Frontiers"])
    for name, term in payload["extension_frontiers"].items():
        lines.append(f"- `{name}`: ready=`{term['frontier_ready']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
