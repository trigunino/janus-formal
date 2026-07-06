"""Algebraic regularity checks for a non-null SO(3) Sigma collar."""

from __future__ import annotations


def regular_sigma_collar_algebra_payload(
    *, A0: float = 1.0, B0: float = 1.0, C0: float = 0.0, R0: float = 1.0
) -> dict:
    if R0 <= 0.0:
        raise ValueError("R0 must be positive")
    det_trho = -float(A0) * float(B0) - float(C0) * float(C0)
    induced_det_over_sin2 = float(A0) * (float(R0) ** 4)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "regular_non_null_Sigma",
        "collar_ansatz": "ds^2=A(rho)dT^2 + 2C(rho)dTdrho - B(rho)drho^2 - R(rho)^2 dOmega^2",
        "sigma_location": "rho=0",
        "inputs": {"A0": A0, "B0": B0, "C0": C0, "R0": R0},
        "det_TRho_block": det_trho,
        "induced_metric_det_over_sin2theta": induced_det_over_sin2,
        "full_collar_block_non_degenerate": det_trho != 0.0,
        "induced_h_ab_non_degenerate": induced_det_over_sin2 != 0.0,
        "regular_hK_pipeline_allowed": det_trho != 0.0 and induced_det_over_sin2 != 0.0,
        "z2_even_regular_policy": {
            "R_even": True,
            "A_even": True,
            "B_even": True,
            "C_odd_implies_C0_zero": C0 == 0.0,
        },
        "key_condition": "regular branch requires A(0) != 0 and R(0)>0; Eddington/PT horizon has A(0)=0",
        "next_required": [
            "derive A0 and B0 from the active bimetric field equations",
            "then compute Christoffels and K_ab in the regular collar",
        ],
    }
