"""Z2/Sigma projected charge reduction to the remaining occupation datum."""

from __future__ import annotations


def z2_projected_charge_reduction_payload() -> dict:
    """Return the no-fit Z2 projection algebra for Dirac Noether charge.

    This does not choose the occupation number. It only removes the artificial
    freedom in projection weights once the deck-invariant sector is selected.
    """

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "Z2_projective_charge_reduction",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "projection_weights_free": False,
        "projection_weights": {
            "N_plus": 0.5,
            "N_minus": 0.5,
        },
        "general_projected_charge_formula": "N_Z2Sigma = (N_plus + N_minus) / 2",
        "deck_invariant_sector": {
            "constraint": "N_plus = N_minus = N_occ",
            "projected_charge_formula": "N_Z2Sigma = N_occ",
            "absolute_N_occ_fixed": False,
        },
        "deck_odd_signed_sector": {
            "constraint": "N_plus = -N_minus",
            "projected_signed_charge_formula": "N_Z2Sigma = 0",
            "physical_baryon_occupation_sector": False,
        },
        "remaining_open_data": ["N_occ"],
        "full_projected_charge_ready": False,
        "primary_blocker": "global_fermion_occupation_number_N_occ_not_fixed",
    }


def reduce_deck_invariant_projected_charge(occupation: float) -> float:
    if occupation <= 0.0:
        raise ValueError("occupation must be positive")
    return float(occupation)


def occupation_degeneracy_payload(occupations: list[float] | None = None) -> dict:
    values = occupations or [1.0, 2.0, 3.0]
    projected = [reduce_deck_invariant_projected_charge(value) for value in values]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "Z2_Noether_occupation_degeneracy",
        "tested_occupations": values,
        "projected_charges": projected,
        "all_satisfy_Z2_deck_invariant_constraint": True,
        "all_satisfy_positive_charge_constraint": True,
        "topology_selects_unique_occupation": False,
        "charge_conservation_selects_unique_occupation": False,
        "primary_blocker": "superselection_state_or_initial_occupation_not_fixed",
    }
