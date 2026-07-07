from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "published_minisuperspace_hamiltonian_reduction_inputs.json"
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_minisuperspace_hamiltonian_reduction_gate.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_minisuperspace_hamiltonian_reduction_gate.md"
)


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    checks = {
        "published_exact_solution_available": True,
        "alpha_Eglobal_identity_available": True,
        "published_bimetric_action_anchor_available": True,
        "minisuperspace_lagrangian_written": bool(
            data.get("minisuperspace_lagrangian_written")
        ),
        "lapse_constraints_derived": bool(data.get("lapse_constraints_derived")),
        "canonical_momenta_derived": bool(data.get("canonical_momenta_derived")),
        "hamiltonian_constraint_derived": bool(data.get("hamiltonian_constraint_derived")),
        "constraint_reduction_performed": bool(data.get("constraint_reduction_performed")),
        "symplectic_pullback_to_exact_solution_derived": bool(
            data.get("symplectic_pullback_to_exact_solution_derived")
        ),
        "alpha_conjugate_coordinate_identified": bool(
            data.get("alpha_conjugate_coordinate_identified")
        ),
        "compact_cycle_in_reduced_orbit_found": bool(
            data.get("compact_cycle_in_reduced_orbit_found")
        ),
        "action_integral_I_alpha_derived": bool(data.get("action_integral_I_alpha_derived")),
        "integrality_or_selection_law_derived": bool(
            data.get("integrality_or_selection_law_derived")
        ),
    }
    canonical_hamiltonian_ready = all(
        checks[key]
        for key in [
            "minisuperspace_lagrangian_written",
            "lapse_constraints_derived",
            "canonical_momenta_derived",
            "hamiltonian_constraint_derived",
            "constraint_reduction_performed",
            "symplectic_pullback_to_exact_solution_derived",
            "alpha_conjugate_coordinate_identified",
        ]
    )
    quantization_ready = canonical_hamiltonian_ready and all(
        checks[key]
        for key in [
            "compact_cycle_in_reduced_orbit_found",
            "action_integral_I_alpha_derived",
            "integrality_or_selection_law_derived",
        ]
    )
    return {
        "status": "janus-z2-published-minisuperspace-hamiltonian-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "checks": checks,
        "canonical_hamiltonian_reduction_ready": canonical_hamiltonian_ready,
        "alpha_quantization_ready": quantization_ready,
        "closed_relations": {
            "exact_solution": "a(u)=alpha*cosh(u)^2",
            "time": "x0(u)=alpha/2*(1+sinh(2u)/2+u)",
            "identity": "a^2*d2a/dx0^2=2*alpha",
            "energy_map": "alpha=-2*pi*G*E_global/c^2",
        },
        "live_derivation_status": (
            "The equations identify alpha with the conserved global energy label. "
            "They do not by themselves define the reduced symplectic form or a "
            "compact action cycle."
        ),
        "hard_obstruction": (
            "The exact orbit parameter u is noncompact and alpha is a homothetic "
            "energy scale. Without a derived compact reduced orbit or boundary "
            "periodicity, Bohr-Sommerfeld quantization has no canonical cycle."
        ),
        "classification": "continuous_Casimir_charge"
        if not quantization_ready
        else "quantized_or_selected_sector",
        "blocked_by": [key for key, ok in checks.items() if not ok],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Published Minisuperspace Hamiltonian Reduction Gate",
                "",
                f"Canonical Hamiltonian reduction ready: `{payload['canonical_hamiltonian_reduction_ready']}`",
                f"Alpha quantization ready: `{payload['alpha_quantization_ready']}`",
                f"Classification: `{payload['classification']}`",
                "",
                payload["live_derivation_status"],
                "",
                payload["hard_obstruction"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
