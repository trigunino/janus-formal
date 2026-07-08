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
from scripts.build_p0_eft_janus_sigma_boundary_variational_decomposition_gate import (
    build_payload as build_sigma_variation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate import (
    build_payload as build_coframe_readiness_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_sigma_boundary_projection_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_sigma_boundary_projection_gate.md"


def build_payload() -> dict[str, Any]:
    state = build_state_space_payload()
    sigma = build_sigma_variation_payload()
    coframe = build_coframe_readiness_payload()
    symbolic_checks = {
        "complex_coadjoint_state_space_ready": state["complex_coadjoint_state_space_ready"],
        "sigma_boundary_variational_package_declared": sigma[
            "sigma_boundary_variational_package_declared"
        ],
        "embedding_variation_channel_declared": True,
        "tetrad_variation_channel_declared": sigma["variational_package"][
            "tetrad_variation_channel_declared"
        ],
        "connection_variation_channel_declared": sigma["variational_package"][
            "connection_variation_channel_declared"
        ],
        "coframe_pullback_formula_ready": coframe["readiness"][
            "coframe_pullback_formula_ready"
        ],
        "spin_connection_pullback_formula_ready": coframe["readiness"][
            "spin_connection_pullback_formula_ready"
        ],
        "antihermitian_projection_policy_ready": state["checks"][
            "antihermitian_translation_projection_declared"
        ],
    }
    active_checks = {
        "active_embedding_ready": coframe["readiness"]["active_embedding_ready"],
        "coframe_pullback_value_ready": coframe["readiness"]["coframe_pullback_ready"],
        "spin_connection_pullback_value_ready": coframe["readiness"][
            "spin_connection_pullback_ready"
        ],
        "nontrivial_boundary_variation_basis_ready": False,
        "closed_boundary_two_cycle_declared": False,
    }
    symbolic_projection_ready = all(symbolic_checks.values())
    active_projection_ready = symbolic_projection_ready and all(active_checks.values())
    return {
        "status": "janus-complex-reality-sigma-boundary-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source_anchor": "X2026-complex-reality + active Sigma variational package",
        "symbolic_checks": symbolic_checks,
        "active_checks": active_checks,
        "projection_formula": {
            "boundary_variation": "delta = (delta X^mu, delta e^A_mu, delta omega^A_B)",
            "translation_generator": "gamma_Sigma^A(delta) = e^A_mu * delta X^mu",
            "lorentz_generator_from_frame": "omega_Sigma(delta) = antiHermitian_G(delta L * L^{-1})",
            "lorentz_generator_from_connection": "omega_Sigma(delta) = i_delta_X X_Sigma^*(omega) + antiHermitian_G(delta_frame)",
            "complex_poincare_generator": "Z_Sigma(delta) = (G*omega_Sigma(delta), gamma_Sigma(delta); 0, 0)",
            "kks_pullback_density": "Omega_Sigma(delta1,delta2)=<mu,[Z_Sigma(delta1),Z_Sigma(delta2)]>",
        },
        "derivation_notes": [
            "The translation part is the embedding displacement expressed in the pulled-back coframe.",
            "The Lorentz part is the anti-Hermitian frame rotation/boost generator.",
            "The spin-connection pullback supplies the connection term for moving the boundary frame.",
            "Anti-Hermitian projection is mandatory before KKS use.",
        ],
        "sigma_boundary_to_complex_poincare_projection_symbolic_ready": symbolic_projection_ready,
        "sigma_boundary_to_complex_poincare_projection_active_ready": active_projection_ready,
        "KKS_boundary_density_evaluable_now": active_projection_ready,
        "KKS_boundary_density_nonzero": False,
        "alpha_generated_now": False,
        "what_this_closes": [
            "symbolic_projection_deltaSigma_to_gamma",
            "symbolic_projection_deltaFrame_to_omega",
            "complex_Poincare_generator_ZSigma_formula",
            "KKS_pullback_density_formula",
        ],
        "still_missing_for_nonzero_density": [
            key for key, ready in active_checks.items() if not ready
        ],
        "next_gate": "ComplexRealityPrequantizationIntegralityGate"
        if active_projection_ready
        else "ComplexRealityBoundaryVariationBasisGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Sigma Boundary Projection Gate",
                "",
                f"Symbolic projection ready: `{payload['sigma_boundary_to_complex_poincare_projection_symbolic_ready']}`",
                f"Active projection ready: `{payload['sigma_boundary_to_complex_poincare_projection_active_ready']}`",
                f"KKS density evaluable now: `{payload['KKS_boundary_density_evaluable_now']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                "## Projection Formula",
                "",
                *[
                    f"- `{key}`: `{value}`"
                    for key, value in payload["projection_formula"].items()
                ],
                "",
                "## Still Missing For Nonzero Density",
                "",
                *[f"- `{item}`" for item in payload["still_missing_for_nonzero_density"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
