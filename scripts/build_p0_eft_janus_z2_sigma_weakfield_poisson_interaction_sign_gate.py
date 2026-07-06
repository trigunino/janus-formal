from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.signed_sector import (
    NewtonianInteraction,
    Sector,
    janus_interaction,
    newtonian_coupling_matrix,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_weakfield_poisson_interaction_sign_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_weakfield_poisson_interaction_sign_gate.json"
)


def build_payload() -> dict:
    matrix = newtonian_coupling_matrix().tolist()
    expected = [[1.0, -1.0], [-1.0, 1.0]]
    interactions = {
        "plus_plus": janus_interaction(Sector.POSITIVE, Sector.POSITIVE).value,
        "minus_minus": janus_interaction(Sector.NEGATIVE, Sector.NEGATIVE).value,
        "plus_minus": janus_interaction(Sector.POSITIVE, Sector.NEGATIVE).value,
        "minus_plus": janus_interaction(Sector.NEGATIVE, Sector.POSITIVE).value,
    }
    same_attract = (
        interactions["plus_plus"] == NewtonianInteraction.ATTRACT.value
        and interactions["minus_minus"] == NewtonianInteraction.ATTRACT.value
    )
    cross_repel = (
        interactions["plus_minus"] == NewtonianInteraction.REPEL.value
        and interactions["minus_plus"] == NewtonianInteraction.REPEL.value
    )
    closure = {
        "active_core_Z2_tunnel_Sigma": True,
        "weak_field_limit_declared": True,
        "two_leaf_Poisson_equations_assumed": True,
        "plus_equation_source_signed": matrix[0] == expected[0],
        "minus_equation_source_signed": matrix[1] == expected[1],
        "same_sector_attraction_derived": same_attract,
        "cross_sector_repulsion_derived": cross_repel,
        "Bondi_runaway_excluded_by_sheet_rules": cross_repel,
        "determinant_ratios_set_to_Newtonian_limit": True,
        "conditional_only": True,
        "does_not_close_tensor_Bianchi": True,
        "does_not_close_R_Sigma_certificate": True,
    }
    return {
        "status": "janus-z2-sigma-weakfield-poisson-interaction-sign-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "conditional_weakfield_two_leaf_Poisson_reduction",
        "poisson_system": {
            "matrix": matrix,
            "expected_matrix": expected,
            "plus_equation": "Delta Phi_plus = 4*pi*G*(rho_plus - rho_minus_abs)",
            "minus_equation": "Delta Phi_minus = 4*pi*G*(-rho_plus + rho_minus_abs)",
        },
        "interactions": interactions,
        "closure": closure,
        "gate_passed": all(closure.values()),
        "conditional_only": True,
        "feeds_main_branch": False,
        "non_closure": [
            "does_not_close_tensor_Bianchi",
            "does_not_close_R_Sigma_solution_certificate",
            "does_not_promote_weakfield_to_full_action",
        ],
        "next_required_if_promoted": [
            "derive_two_leaf_Poisson_equations_from_active_Z2Sigma_field_equations",
            "derive_Newtonian_limit_B_plus_equals_B_minus_equals_one",
            "connect_weakfield_sources_to_Bianchi_compatible_K_plus_K_minus",
        ],
        "interpretation": (
            "Conditionally, once the two-leaf weak-field Poisson equations hold, "
            "same-sector attraction and cross-sector repulsion follow from the sign matrix. "
            "This is a Newtonian diagnostic, not a full tensor/Bianchi closure."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Weak-Field Poisson Interaction Sign Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Conditional only: `{payload['conditional_only']}`",
        "",
        payload["interpretation"],
        "",
        "## Poisson System",
        f"- `matrix`: `{payload['poisson_system']['matrix']}`",
        f"- `plus`: `{payload['poisson_system']['plus_equation']}`",
        f"- `minus`: `{payload['poisson_system']['minus_equation']}`",
        "",
        "## Non Closure",
    ]
    lines.extend(f"- `{item}`" for item in payload["non_closure"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
