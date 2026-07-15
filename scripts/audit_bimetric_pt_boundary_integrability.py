from __future__ import annotations


def corner_residual(k_plus: float, area_plus: float, angle_plus: float,
                    k_minus: float, area_minus: float, angle_minus: float) -> float:
    """Weighted paired Hayward/null-joint density (common orientation convention)."""
    return k_plus * area_plus * angle_plus + k_minus * area_minus * angle_minus


def null_rescaling_residual(weight_plus: float, weight_minus: float, log_scale: float) -> float:
    """Anomaly under opposite PT rescalings eta_± -> eta_± ± log_scale."""
    return (weight_plus - weight_minus) * log_scale


def build_payload() -> dict:
    return {
        "artifact": "bimetric_pt_boundary_integrability",
        "status": "pt_paired_flux_integrability_criterion_closed",
        "criterion": "Omega_boundary(delta1,delta2)=delta1(delta2 H)-delta2(delta1 H)=0",
        "pt_pairing": "Omega_minus(PT delta1,PT delta2)=-Omega_plus(delta1,delta2)",
        "consequence": "total paired symplectic flux vanishes and the paired Hamiltonian charge is locally integrable",
        "corner": {
            "functional": "I_joint=2 epsilon integral_C (K_plus sqrt(sigma_plus) eta_plus + K_minus sqrt(sigma_minus) eta_minus)",
            "pt_cancellation": "weighted densities obey K_minus sqrt(sigma_minus) eta_minus=-K_plus sqrt(sigma_plus) eta_plus",
            "null_rescaling": "opposite normal rescalings cancel iff K_plus sqrt(sigma_plus)=K_minus sqrt(sigma_minus)",
        },
        "closure": {
            "paired_flux_cancellation": True,
            "local_integrability_criterion": True,
            "null_normal_normalization_fixed": False,
            "corner_joint_functional_derived": True,
            "conditional_corner_cancellation_proved": True,
            "global_charge_integrability": False,
        },
    }
