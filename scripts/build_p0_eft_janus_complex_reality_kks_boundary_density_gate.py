from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_coadjoint_state_space_gate import (
    build_payload as build_state_space_payload,
)
from scripts.build_p0_eft_janus_z2_pt_souriau_omega_from_theta_gate import (
    build_payload as build_pt_theta_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_kks_boundary_density_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_kks_boundary_density_gate.md"


def build_payload() -> dict[str, Any]:
    state = build_state_space_payload()
    pt_theta = build_pt_theta_payload()
    finite_kks = {
        "formula": "Omega_mu(ad*_X mu, ad*_Y mu) = <mu,[X,Y]>",
        "pairing": "1/2 Tr(M*omega_bracket)+P_dagger*G*gamma_bracket",
        "nonzero_witness": {
            "P": "e0",
            "X": "boost_01",
            "Y": "translation_e1",
            "bracket_translation": "e0",
            "Omega_value": 1.0,
        },
        "global_finite_dimensional_KKS_nonzero": True,
    }
    boundary_checks = {
        "complex_coadjoint_state_space_ready": state["complex_coadjoint_state_space_ready"],
        "finite_dimensional_KKS_formula_ready": True,
        "finite_dimensional_KKS_nonzero": finite_kks[
            "global_finite_dimensional_KKS_nonzero"
        ],
        "sigma_boundary_phase_space_declared": False,
        "sigma_variations_mapped_to_complex_lie_algebra": False,
        "pt67_theta_route_nontrivial": pt_theta["integrality_route_open"],
        "boundary_two_cycle_with_nonzero_period_declared": False,
        "density_on_sigma_nonzero": False,
    }
    boundary_ready = all(boundary_checks.values())
    return {
        "status": "janus-complex-reality-kks-boundary-density-gate",
        "source_anchor": "X2026-complex-reality plus active Z2/Sigma PT route",
        "finite_kks_result": finite_kks,
        "boundary_checks": boundary_checks,
        "global_KKS_orbit_nonzero": True,
        "KKS_boundary_density_ready": boundary_ready,
        "KKS_boundary_density_nonzero": False,
        "alpha_generated_now": False,
        "important_distinction": (
            "The complex-reality paper is enough to define a nonzero finite "
            "coadjoint-orbit KKS form. It is not enough to define a nonzero "
            "Sigma boundary density because the map from Sigma boundary "
            "variations to complex Poincare generators is not derived."
        ),
        "current_blockers": [
            key for key, ok in boundary_checks.items() if not ok
        ],
        "next_gate": "ComplexRealitySigmaBoundaryProjectionGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality KKS Boundary Density Gate",
                "",
                f"Global KKS nonzero: `{payload['global_KKS_orbit_nonzero']}`",
                f"KKS boundary density ready: `{payload['KKS_boundary_density_ready']}`",
                f"KKS boundary density nonzero: `{payload['KKS_boundary_density_nonzero']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                payload["important_distinction"],
                "",
                "## Current Blockers",
                "",
                *[f"- `{item}`" for item in payload["current_blockers"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
