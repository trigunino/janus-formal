"""Bianchi-balance extraction for Janus Z2 cover projected equations."""

from __future__ import annotations

import json
from pathlib import Path


def derive_bianchi_balances(payload: dict) -> dict:
    if payload.get("active_core") != "JanusZ2CoverMasterAction":
        raise ValueError("active_core must be JanusZ2CoverMasterAction")
    if not payload.get("projected_equations_ready"):
        raise ValueError("projected equations must be ready")
    if payload.get("rho_eff_shortcut_used") is not False:
        raise ValueError("rho_eff shortcut must be false")
    if payload.get("negative_thermodynamic_density_postulated") is not False:
        raise ValueError("negative thermodynamic density postulate must be false")
    if payload.get("archived_z4_reuse_used") is not False:
        raise ValueError("archived Z4 reuse must be false")

    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "bianchi_balance_from_projected_equations",
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "balances": {
            "plus": (
                "D_plus J_Sigma_plus = -D_plus[kappa_J * "
                "(T_plus - B_minus_to_plus * T_minus_to_plus)]"
            ),
            "minus": (
                "D_minus J_Sigma_minus = -D_minus[kappa_J * "
                "(T_minus - B_plus_to_minus * T_plus_to_minus)]"
            ),
        },
        "closed_if": {
            "self_sector_noether_conservation": "D_plus T_plus = 0 and D_minus T_minus = 0",
            "cross_measure_transport": (
                "D_plus(B_minus_to_plus*T_minus_to_plus) and "
                "D_minus(B_plus_to_minus*T_plus_to_minus) are derived from tau_Z2"
            ),
            "sigma_variation": "J_Sigma_plus/minus are derived from delta S_master/delta X_Sigma",
        },
        "paired_bianchi_balance_ready": True,
        "paired_bianchi_closed": False,
        "primary_blocker": "derive_cross_measure_transport_and_sigma_variation",
    }


def attach_sigma_source_to_bianchi_balance(balance_payload: dict, sigma_payload: dict) -> dict:
    if balance_payload.get("active_core") != "JanusZ2CoverMasterAction":
        raise ValueError("balance active_core must be JanusZ2CoverMasterAction")
    if sigma_payload.get("active_core") != "JanusZ2CoverMasterAction":
        raise ValueError("sigma active_core must be JanusZ2CoverMasterAction")
    if not balance_payload.get("paired_bianchi_balance_ready"):
        raise ValueError("Bianchi balance must be ready")
    if not sigma_payload.get("sigma_source_ready"):
        raise ValueError("Sigma source must be ready")
    out = dict(balance_payload)
    out["sigma_source_attached"] = True
    out["sigma_junction_derived"] = bool(sigma_payload.get("sigma_junction_derived"))
    out["sigma_source_components"] = {
        "plus_tau": sigma_payload["J_Sigma_plus_tau"],
        "plus_s": sigma_payload["J_Sigma_plus_s"],
        "minus_tau": sigma_payload["J_Sigma_minus_tau"],
        "minus_s": sigma_payload["J_Sigma_minus_s"],
    }
    out["paired_bianchi_closed"] = False
    out["primary_blocker"] = "derive_divergence_of_sigma_source_and_cross_measure_transport"
    return out


def load_and_derive_bianchi_balances(path: Path) -> dict:
    return derive_bianchi_balances(json.loads(Path(path).read_text(encoding="utf-8")))
