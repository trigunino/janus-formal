"""Projection algebra for a single Janus Z2 cover master action."""

from __future__ import annotations

import json
from pathlib import Path


FORBIDDEN_TEXT = ("planck", "lcdm", "z4", "fit", "bao_scan", "rho_eff")
REQUIRED_FALSE_FLAGS = [
    "compressed_planck_lcdm_used",
    "archived_z4_reuse_used",
    "observational_fit_used",
    "rho_eff_shortcut_used",
    "negative_thermodynamic_density_postulated",
    "two_independent_actions_used",
    "full_no_fit_prediction_ready",
]


def _clean_symbol(payload: dict, key: str) -> str:
    value = str(payload.get(key, "")).strip()
    if not value:
        raise ValueError(f"{key} must be nonempty")
    lowered = value.lower()
    if any(token in lowered for token in FORBIDDEN_TEXT):
        raise ValueError(f"{key} contains forbidden shortcut/provenance: {value}")
    return value


def _require_sign(payload: dict, key: str, expected: int) -> int:
    value = int(payload.get(key))
    if value != expected:
        raise ValueError(f"{key} must be {expected}")
    return value


def derive_projected_equations(payload: dict) -> dict:
    if payload.get("active_core") != "JanusZ2CoverMasterAction":
        raise ValueError("active_core must be JanusZ2CoverMasterAction")
    if payload.get("source") != "explicit_master_action_projection":
        raise ValueError("source must be explicit_master_action_projection")
    for flag in REQUIRED_FALSE_FLAGS:
        if payload.get(flag) is not False:
            raise ValueError(f"{flag} must be false")

    kappa = _clean_symbol(payload, "kappa_symbol")
    b_minus_to_plus = _clean_symbol(payload, "B_minus_to_plus")
    b_plus_to_minus = _clean_symbol(payload, "B_plus_to_minus")
    sigma_plus = _clean_symbol(payload, "Sigma_plus_boundary_source")
    sigma_minus = _clean_symbol(payload, "Sigma_minus_boundary_source")
    _require_sign(payload, "self_sector_orientation_sign", 1)
    cross_sign = _require_sign(payload, "cross_sector_orientation_sign", -1)

    cross = "-" if cross_sign < 0 else "+"
    plus_rhs = f"{kappa} * (T_plus {cross} {b_minus_to_plus} * T_minus_to_plus) + {sigma_plus}"
    minus_rhs = f"{kappa} * (T_minus {cross} {b_plus_to_minus} * T_plus_to_minus) + {sigma_minus}"
    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "projected_equations_from_single_master_action",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "two_independent_actions_used": False,
        "full_no_fit_prediction_ready": False,
        "orientation_signs": {
            "self_sector_orientation_sign": 1,
            "cross_sector_orientation_sign": cross_sign,
        },
        "projected_equations": {
            "E_plus": f"G_plus = {plus_rhs}",
            "E_minus": f"G_minus = {minus_rhs}",
        },
        "physical_interpretation": {
            "negative_gravity_origin": "cross-sector projection orientation sign",
            "not_negative_thermodynamic_density": True,
            "not_rho_eff_collapse": True,
        },
        "paired_bianchi_targets": {
            "plus": f"D_plus(G_plus - ({plus_rhs})) = 0",
            "minus": f"D_minus(G_minus - ({minus_rhs})) = 0",
            "source": "master-action diffeomorphism invariance",
        },
        "sigma_junction_target": (
            "delta_S_master/delta_X_Sigma = 0 gives the junction equation; "
            "Sigma_plus_boundary_source and Sigma_minus_boundary_source are not independent fits"
        ),
        "projected_equations_ready": True,
        "sigma_junction_derived": False,
        "paired_bianchi_derived": False,
    }


def load_and_derive_projected_equations(path: Path) -> dict:
    return derive_projected_equations(json.loads(Path(path).read_text(encoding="utf-8")))
