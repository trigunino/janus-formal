from __future__ import annotations

import json
import os
from pathlib import Path


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))


def build_payload() -> dict:
    spatial_phase_dimension = 24
    diagonal_first_class = 4
    bd_second_class = 2
    physical_phase_dimension = (
        spatial_phase_dimension - 2 * diagonal_first_class - bd_second_class
    )
    return {
        "artifact": "bimetric_adm_bd_constraint_audit",
        "status": "candidate_A_inherits_Hassan_Rosen_BD_removal_on_admissible_domain",
        "candidate_match": {
            "two_positive_einstein_hilbert_terms": True,
            "single_elementary_symmetric_square_root_potential": True,
            "separate_minimal_matter_couplings": True,
            "cross_metric_matter_coupling_absent": True,
        },
        "shift_redefinition": {
            "form": "N_plus^i-N_minus^i=(N_minus*delta^i_j+N_plus*D^i_j)n^j",
            "auxiliary_shift_equations_lapse_independent": True,
            "interaction_affine_in_both_lapses_after_redefinition": True,
            "required_domain": "real square root and locally invertible shift map",
        },
        "dirac_chain": [
            "lapse variation gives the extra Hamiltonian constraint C=0",
            "time preservation gives the secondary constraint C2={C,H}=0",
            "preservation of C2 fixes the remaining relative lapse combination",
        ],
        "count": {
            "spatial_phase_dimension": spatial_phase_dimension,
            "diagonal_first_class_constraints": diagonal_first_class,
            "bd_second_class_constraints": bd_second_class,
            "physical_phase_dimension": physical_phase_dimension,
            "configuration_degrees_of_freedom": physical_phase_dimension // 2,
            "spectrum": "2 massless + 5 massive spin-2 polarizations",
        },
        "closure": {
            "bd_scalar_pair_removed": physical_phase_dimension == 14,
            "full_functional_bracket_mechanized_in_repo": False,
            "published_hr_theorem_imported_conditionally": True,
            "global_square_root_domain_proved": False,
            "shift_map_global_invertibility_proved": False,
        },
        "references": ["arXiv:1109.3230", "arXiv:1111.2070"],
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "bimetric_adm_bd_constraint_audit.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
