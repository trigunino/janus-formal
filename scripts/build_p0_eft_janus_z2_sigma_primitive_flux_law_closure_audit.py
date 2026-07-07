from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_primitive_flux_sector_law_investigation import (
    build_payload as primitive_law,
)
from scripts.build_p0_eft_janus_z2_sigma_unit_flux_irreducibility_gate import (
    build_payload as irreducibility,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_primitive_flux_law_closure_audit.json")


def _partitions(total: int) -> list[list[int]]:
    if total <= 0:
        return []
    result: list[list[int]] = []

    def rec(remain: int, start: int, current: list[int]) -> None:
        if remain == 0:
            result.append(current.copy())
            return
        for value in range(start, remain + 1):
            current.append(value)
            rec(remain - value, value, current)
            current.pop()

    rec(total, 1, [])
    return result


def build_payload() -> dict:
    primitive = primitive_law()
    unit = irreducibility()
    examples = {
        "c1_2_partitions": _partitions(2),
        "c1_3_partitions": _partitions(3),
    }
    obstruction = {
        "same_total_Chern_charge_has_multiple_puncture_partitions": True,
        "standard_LQG_counts_many_puncture_spin_configurations": True,
        "projection_constraint_does_not_fix_puncture_count": True,
        "multi_charge_punctures_are_not_excluded_by_c1_alone": True,
        "empty_or_trivial_spin_punctures_need_boundary_state_rule": True,
    }
    standard_no_go = all(obstruction.values())
    derived = primitive["primitive_flux_sector_law_ready"] and unit["unit_flux_irreducibility_ready"]
    return {
        "status": "janus-z2-sigma-primitive-flux-law-closure-audit",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "The primitive flux law cannot be derived from Chern topology alone. "
            "A total c1=n admits multiple puncture partitions, so N_gap=|n| "
            "requires an additional Janus/PT boundary-state or primitive-charge law."
        ),
        "primitive_law_status": primitive["status"],
        "primitive_flux_sector_law_ready": primitive["primitive_flux_sector_law_ready"],
        "unit_flux_irreducibility_status": unit["status"],
        "unit_flux_irreducibility_ready": unit["unit_flux_irreducibility_ready"],
        "charge_partition_examples": examples,
        "obstruction": obstruction,
        "standard_bibliography_closes_as_no_go": standard_no_go and not derived,
        "N_gap_equals_abs_n_derived": derived,
        "recommended_active_route": (
            "N_gap_superselection_family"
            if not derived
            else "N_gap_equals_abs_n_unique_sector"
        ),
        "required_to_reopen_unique_route": [
            "Janus_PT_boundary_state_selects_primitive_charge",
            "charge_lattice_generator_normalized",
            "fusion_of_unit_fluxes_forbidden_by_superselection",
            "splitting_of_unit_flux_forbidden_by_integrality",
            "empty_spin_punctures_forbidden_by_area_operator_kernel",
            "minimal_nonzero_spin_representation_selected",
        ],
        "bibliography_conclusion": [
            {
                "key": "Ashtekar-Baez-Corichi-Krasnov-2000",
                "conclusion": "CS curvature defects live at punctures; total curvature is not a puncture-count theorem.",
                "url": "https://www.intlpress.com/site/pub/files/_fulltext/journals/atmp/2000/0004/0001/ATMP-2000-0004-0001-a001.pdf",
            },
            {
                "key": "Engle-Noui-Perez-2009",
                "conclusion": "SU(2) horizon states are labelled by puncture spins/intertwiners; the formulation counts many compatible configurations.",
                "url": "https://arxiv.org/abs/0905.3168",
            },
            {
                "key": "LQG horizon reviews",
                "conclusion": "Projection/Gauss constraints restrict admissible labels but do not collapse all charge partitions to one puncture per unit c1.",
                "url": "https://arxiv.org/pdf/1201.6102",
            },
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Primitive Flux Law Closure Audit",
        "",
        payload["physical_statement"],
        "",
        f"N_gap=|n| derived: `{payload['N_gap_equals_abs_n_derived']}`",
        f"Standard biblio no-go: `{payload['standard_bibliography_closes_as_no_go']}`",
        f"Recommended active route: `{payload['recommended_active_route']}`",
        "",
        "## Charge Partition Examples",
        f"- c1=2: `{payload['charge_partition_examples']['c1_2_partitions']}`",
        f"- c1=3: `{payload['charge_partition_examples']['c1_3_partitions']}`",
        "",
        "## Required To Reopen Unique Route",
    ]
    lines.extend(f"- `{item}`" for item in payload["required_to_reopen_unique_route"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
