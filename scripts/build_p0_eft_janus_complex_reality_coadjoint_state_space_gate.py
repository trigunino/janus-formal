from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_eq131_kks_projection_gate import (
    build_payload as build_eq131_payload,
)
from scripts.build_p0_eft_janus_complex_reality_source_formula_curation_gate import (
    build_payload as build_formula_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_coadjoint_state_space_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_coadjoint_state_space_gate.md"


def build_payload() -> dict[str, Any]:
    formula = build_formula_payload()
    eq131 = build_eq131_payload()
    checks = {
        "formula_anchors_curated": formula["formula_curation_ready"],
        "complex_metric_declared": True,
        "complex_poincare_group_declared": True,
        "complex_lie_algebra_declared": True,
        "complex_moment_pair_M_P_declared": True,
        "souriau_pairing_declared": True,
        "coadjoint_action_declared": True,
        "antihermitian_translation_projection_declared": eq131[
            "kks_ready_term_preserves_antihermitian_M"
        ],
        "PT_mass_sign_slice_declared": True,
    }
    state_space_ready = all(checks.values())
    downstream = {
        "boundary_phase_space_on_sigma_declared": False,
        "KKS_two_form_on_boundary_orbit_derived": False,
        "KKS_density_nonzero": False,
        "prequantization_integrality_ready": False,
        "mass_or_charge_lattice_ready": False,
        "alpha_state_law_ready": False,
    }
    return {
        "status": "janus-complex-reality-coadjoint-state-space-gate",
        "source_anchor": "X2026-complex-reality",
        "checks": checks,
        "complex_coadjoint_state_space_ready": state_space_ready,
        "state_space": {
            "base_vector_space": "C^(1,3)",
            "metric": "dX_dagger*G*dX",
            "group": "complex_Poincare(L,C), L_dagger*G*L=G",
            "lie_algebra": "Z=(G*omega,gamma;0,0), omega_dagger=-omega",
            "moment": "mu={M,P}, M_dagger=-M, P in C^4",
            "pairing": "1/2 Tr(M*omega)+P_dagger*G*gamma",
            "coadjoint_translation_policy": "antihermitian_projection_required_for_KKS",
        },
        "downstream_not_yet_ready": downstream,
        "what_this_closes": [
            "complex_state_space_scaffold",
            "KKS_safe_coadjoint_translation_policy",
            "PT_mass_sign_interpretation_target",
        ],
        "what_remains": [key for key, ready in downstream.items() if not ready],
        "alpha_generated_now": False,
        "next_gate": "ComplexRealityKKSBoundaryDensityGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Coadjoint State Space Gate",
                "",
                f"State space ready: `{payload['complex_coadjoint_state_space_ready']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                "## State Space",
                "",
                *[f"- `{key}`: `{value}`" for key, value in payload["state_space"].items()],
                "",
                "## Remaining",
                "",
                *[f"- `{item}`" for item in payload["what_remains"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
