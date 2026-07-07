from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_brown_york_boundary_charge_reduction_gate import (
    build_payload as build_brown_york,
)
from scripts.build_p0_eft_janus_z2_sigma_boundary_lapse_normalization_gate import (
    build_payload as build_lapse,
)
from scripts.build_p0_eft_janus_z2_sigma_boundary_surface_measure_gate import (
    build_payload as build_surface_measure,
)
from scripts.derive_p0_eft_janus_z2_sigma_souriau_boundary_hamiltonian_attempt import (
    build_payload as build_souriau,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_noether_hamiltonian_boundary_charge_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_noether_hamiltonian_boundary_charge_gate.json"
)


def build_payload() -> dict:
    brown_york = build_brown_york()
    lapse = build_lapse()
    surface = build_surface_measure()
    souriau = build_souriau()
    closure = {
        "covariant_phase_space_formula_declared": True,
        "time_generator_declared": True,
        "reference_subtraction_declared": True,
        "brown_york_equivalence_declared": True,
        "charge_kind_fixed_as_energy": True,
        "souriau_global_charge_not_local_density": True,
        "boundary_charge_value_available": False,
        "symbolic_surface_measure_available": surface["symbolic_surface_measure_ready"],
        "absolute_surface_measure_available": surface["numeric_surface_measure_ready"],
        "dimensionless_lapse_available": lapse["dimensionless_lapse_ready"],
        "physical_lapse_normalization_available": lapse["physical_lapse_ready"],
    }
    return {
        "status": "janus-z2-sigma-noether-hamiltonian-boundary-charge-gate",
        "active_core": "Z2_tunnel_Sigma",
        "charge_kind": "Hamiltonian_boundary_energy",
        "covariant_phase_space_formula": (
            "delta H_xi = integral_Sigma (delta Q_xi - i_xi theta), "
            "with xi = N u tangent to the active Z2/Sigma boundary time flow"
        ),
        "brown_york_reduction": (
            "For the Dirichlet metric boundary ensemble this reduces to "
            "E_BY = kappa^-1 integral_Sigma N sqrt(q) (k_ref-k_phys)."
        ),
        "symbolic_charge": brown_york["known_inputs"]["symbolic_E_BY_for_eps_minus_one"],
        "souriau_relation": {
            "moment_map_charge": souriau["deck_invariant_charge_reduction"],
            "hamiltonian_candidate": souriau["boundary_hamiltonian_candidate"],
            "local_density_available": souriau["local_density_from_charge_available"],
        },
        "lapse_gate": {
            "status": lapse["status"],
            "dimensionless_lapse_ready": lapse["dimensionless_lapse_ready"],
            "physical_lapse_ready": lapse["physical_lapse_ready"],
        },
        "surface_measure_gate": {
            "status": surface["status"],
            "formula": surface["surface_measure_formula"],
            "symbolic_ready": surface["symbolic_surface_measure_ready"],
            "numeric_ready": surface["numeric_surface_measure_ready"],
        },
        "closure": closure,
        "symbolic_boundary_hamiltonian_ready": all(
            closure[key]
            for key in [
                "covariant_phase_space_formula_declared",
                "time_generator_declared",
                "reference_subtraction_declared",
                "brown_york_equivalence_declared",
                "charge_kind_fixed_as_energy",
            ]
        ),
        "numeric_boundary_hamiltonian_ready": all(closure.values()),
        "blocked_by": [key for key, ok in closure.items() if not ok],
        "forbidden_shortcuts": [
            "do_not_treat_Souriau_global_charge_as_surface_density",
            "do_not_choose_lapse_or_surface_measure_by_fit",
            "do_not_promote_reference_subtraction_zero_to_nonzero_H0",
        ],
        "next_required": [
            "derive_absolute_surface_measure_or_RSigma",
            "derive_physical_time_scale_for_boundary_lapse",
            "then_evaluate_E_boundary_J_or_Q_boundary_kg",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Noether Hamiltonian Boundary Charge Gate",
        "",
        f"Charge kind: `{payload['charge_kind']}`",
        f"Symbolic boundary Hamiltonian ready: `{payload['symbolic_boundary_hamiltonian_ready']}`",
        f"Numeric boundary Hamiltonian ready: `{payload['numeric_boundary_hamiltonian_ready']}`",
        "",
        "## Formula",
        payload["covariant_phase_space_formula"],
        payload["brown_york_reduction"],
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
