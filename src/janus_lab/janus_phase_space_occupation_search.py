"""Search candidates for the Janus photon phase-space occupation law.

The early-plasma extension found a precise target: a thermal cooling branch
needs an occupation/phase-space multiplier scaling as a^3. This module tests
candidate mechanisms against that exponent without treating them as proven.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations_with_replacement
import json
import math
from pathlib import Path


REQUIRED_OCCUPATION_EXPONENT = 3.0


def _distinct_degree_sums(weights: list[int], degree: int) -> int:
    return len({sum(combo) for combo in combinations_with_replacement(weights, degree)})


def _read_json_if_present(path: Path) -> dict | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class OccupationMechanismCandidate:
    name: str
    family: str
    exponent: float | None
    status: str
    reason: str
    next_required: str

    @property
    def matches_required_exponent(self) -> bool:
        return self.exponent == REQUIRED_OCCUPATION_EXPONENT


def occupation_mechanism_candidates() -> list[OccupationMechanismCandidate]:
    return [
        OccupationMechanismCandidate(
            name="z2_sheet_multiplicity",
            family="topological_constant",
            exponent=0.0,
            status="rejected",
            reason="A two-fold cover changes normalization by 2, not a scale-factor exponent.",
            next_required="none; cannot produce a^3",
        ),
        OccupationMechanismCandidate(
            name="rp3_or_sigma_topology_constant",
            family="topological_constant",
            exponent=0.0,
            status="rejected",
            reason="Topology fixes identifications/cycles, not an expanding occupation factor by itself.",
            next_required="none; topology needs a geometric scale law to become dynamical",
        ),
        OccupationMechanismCandidate(
            name="sigma_area_modes",
            family="geometric_boundary_modes",
            exponent=2.0,
            status="insufficient",
            reason="Area modes scale like a^2, one power short of the required a^3.",
            next_required="derive an additional radial/normal mode or reject",
        ),
        OccupationMechanismCandidate(
            name="sigma_volume_modes",
            family="geometric_bulk_modes",
            exponent=3.0,
            status="candidate",
            reason="A 3D active throat/collar mode volume naturally gives a^3.",
            next_required="derive that visible photons count collar volume modes, not only Sigma area modes",
        ),
        OccupationMechanismCandidate(
            name="horizon_volume_modes",
            family="causal_volume_modes",
            exponent=3.0,
            status="candidate",
            reason="With Eq40 c/H length scaling can give a causal volume scaling like a^3.",
            next_required="derive the relevant Janus pre-drag H_J scaling and causal-volume coupling",
        ),
        OccupationMechanismCandidate(
            name="quantum_cell_h3_deformation",
            family="variable_quantum_cell",
            exponent=-4.5,
            status="rejected",
            reason="h^3 scales as a^(9/2), but the state-density factor is inverse and has the wrong exponent.",
            next_required="none unless the phase-space measure is redefined",
        ),
        OccupationMechanismCandidate(
            name="compton_cutoff_mode_count",
            family="uv_cutoff_modes",
            exponent=0.0,
            status="rejected",
            reason="Both physical volume and Compton wavelength cubed scale as a^3, so their ratio is constant.",
            next_required="none; no a^3 occupation factor",
        ),
        OccupationMechanismCandidate(
            name="adiabatic_radiation_first_law",
            family="thermodynamic_consistency",
            exponent=3.0,
            status="conditional_candidate",
            reason=(
                "If visible radiation obeys d(rho V)+p dV=0 with p=rho/3, then rho_gamma~a^-4. "
                "Under Eq40 blackbody counting this forces an a^3 occupation factor to conserve photon entropy/number."
            ),
            next_required="derive the radiation first law in the variable-constants Janus/Z2 frame",
        ),
        OccupationMechanismCandidate(
            name="negative_sector_entropy_projection",
            family="two_sector_projection",
            exponent=None,
            status="open_symbolic",
            reason="Could match a^3 only if the plus/minus volume or entropy projection has the right scaling.",
            next_required="derive plus/minus entropy projection law and evaluate its exponent",
        ),
    ]


def occupation_search_payload() -> dict:
    candidates = occupation_mechanism_candidates()
    matching = [candidate.name for candidate in candidates if candidate.matches_required_exponent]
    viable = [
        candidate.name
        for candidate in candidates
        if candidate.status in {"candidate", "conditional_candidate", "open_symbolic"}
    ]
    return {
        "status": "janus-phase-space-occupation-search",
        "required_occupation_exponent": REQUIRED_OCCUPATION_EXPONENT,
        "candidate_count": len(candidates),
        "matching_exponent_candidates": matching,
        "viable_or_open_candidates": viable,
        "best_current_candidate": "adiabatic_radiation_first_law",
        "candidates": [
            {
                "name": candidate.name,
                "family": candidate.family,
                "exponent": candidate.exponent,
                "matches_required_exponent": candidate.matches_required_exponent,
                "status": candidate.status,
                "reason": candidate.reason,
                "next_required": candidate.next_required,
            }
            for candidate in candidates
        ],
        "bottom_line": (
            "The a^3 factor is not arbitrary if it is derived as the correction required "
            "to reconcile Eq40 blackbody phase-space counting with an adiabatic radiation "
            "fluid law. The hard step is now deriving that radiation first law in the "
            "Janus/Z2 variable-constants frame."
        ),
    }


def adiabatic_radiation_first_law_derivation_payload() -> dict:
    """Conditional derivation of the required occupation exponent.

    In a plus-sector FLRW frame, separate conservation of a traceless radiation
    stress tensor gives d(rho V)+p dV=0 with p=rho/3 and V~a^3, hence
    rho_gamma~a^-4. Eq40 blackbody counting with T_energy~a^-1 and h*c~a
    gives bare n_gamma~a^-6. To keep photon number/entropy in a comoving volume
    fixed, the occupation multiplier must scale as a^3.
    """

    volume_exponent = 3.0
    equation_of_state_w = 1.0 / 3.0
    rho_gamma_exponent = -3.0 * (1.0 + equation_of_state_w)
    temperature_energy_exponent = -1.0
    hc_exponent = 1.0
    bare_blackbody_number_exponent = 3.0 * (temperature_energy_exponent - hc_exponent)
    target_number_exponent = -volume_exponent
    occupation_exponent = target_number_exponent - bare_blackbody_number_exponent
    return {
        "status": "janus-adiabatic-radiation-first-law-derivation",
        "conditional_inputs": {
            "plus_sector_visible_photon_stress_conserved": "required",
            "radiation_tracefree_w_equals_one_third": True,
            "visible_volume_scales_as_a3": True,
            "Eq40_hc_scales_as_a": True,
            "thermal_energy_temperature_scales_as_a_minus_1": "required_or_derived_from_radiation_fluid",
        },
        "derived_exponents": {
            "rho_gamma": rho_gamma_exponent,
            "bare_blackbody_n_gamma": bare_blackbody_number_exponent,
            "target_conserved_n_gamma": target_number_exponent,
            "required_occupation": occupation_exponent,
        },
        "occupation_exponent_matches_target": occupation_exponent == REQUIRED_OCCUPATION_EXPONENT,
        "conditional_closure": occupation_exponent == REQUIRED_OCCUPATION_EXPONENT,
        "remaining_non_rustine_proof_obligations": [
            "accept or replace the plus-sector Maxwell action extension contract",
            "prove the occupation multiplier is an actual phase-space/entropy density, not a post-hoc degeneracy",
        ],
    }


def plus_sector_photon_stress_conservation_payload() -> dict:
    """Ledger for deriving visible-photon stress conservation.

    The repo has paper anchors for distinct plus/minus photon geodesics and an
    existing same-sector Noether stress scaffold. It does not yet contain an
    explicit plus-sector Maxwell/radiation action, so the radiation first law is
    still conditional on materializing that action and its equations of motion.
    """

    anchors = {
        "M15_positive_photons_follow_g_plus": True,
        "M30_distinct_geodesic_families": True,
        "same_sector_noether_stress_scaffold_exists": True,
    }
    required_action_inputs = {
        "plus_sector_photon_action_declared": True,
        "minimal_coupling_to_g_plus": True,
        "diffeomorphism_invariance_declared": True,
        "photon_eom_declared": True,
        "no_cross_sector_photon_exchange_declared": True,
        "paper_native_explicit_formula": False,
        "extension_contract": "standard_plus_sector_maxwell_radiation_action",
    }
    conditional_noether_derivation = {
        "if_S_gamma_plus_minimally_coupled_to_g_plus": "nabla_plus_T_gamma_plus_equals_zero",
        "if_photon_stress_tracefree": "radiation_first_law_rho_gamma_scales_a_minus_4",
        "feeds_occupation_a3_derivation": True,
    }
    missing = [
        "connect plus-sector conservation to the Janus variable-constants thermal frame",
        "decide whether standard Maxwell completion is accepted as model extension or kept as paper-external",
    ]
    return {
        "status": "janus-plus-sector-photon-stress-conservation",
        "anchors": anchors,
        "required_action_inputs": required_action_inputs,
        "conditional_noether_derivation": conditional_noether_derivation,
        "plus_sector_photon_stress_conservation_conditionally_derived": True,
        "plus_sector_photon_stress_conservation_unconditionally_derived_within_extension": True,
        "plus_sector_photon_stress_conservation_paper_native": False,
        "radiation_first_law_unblocked_within_extension": True,
        "remaining_non_rustine_proof_obligations": missing,
        "bottom_line": (
            "With the standard plus-sector Maxwell action accepted as an "
            "extension contract, Noether closes visible photon stress "
            "conservation. This is still not paper-native: it must be kept "
            "separate from strict reference reproduction."
        ),
    }


def plus_sector_maxwell_radiation_action_payload() -> dict:
    """Standard electromagnetic completion for the plus photon sector."""

    return {
        "status": "janus-plus-sector-maxwell-radiation-action",
        "action_contract": {
            "field": "A_plus",
            "metric": "g_plus",
            "density": "-1/4 sqrt_abs_g_plus F_plus_mn F_plus^mn",
            "coupling": "minimal_to_g_plus",
            "cross_sector_exchange": "forbidden_at_this_stage",
        },
        "derived_objects": {
            "maxwell_eom": "nabla_plus_mu F_plus^mu_nu = 0 in vacuum/radiation era",
            "stress_tensor": (
                "T_gamma_plus_mn = F_mr F_n^r - 1/4 g_plus_mn F_rs F^rs"
            ),
            "trace": "zero in four dimensions",
            "noether_identity": "nabla_plus_mu T_gamma_plus^mu_nu = 0 on shell",
            "radiation_fluid_limit": "p_gamma = rho_gamma/3",
        },
        "paper_relation": {
            "compatible_with_M15_M30_photon_geodesic_anchors": True,
            "explicitly_given_by_paper": False,
            "classification": "minimal_standard_extension",
        },
        "unblocks": {
            "plus_sector_photon_stress_conservation": True,
            "adiabatic_radiation_first_law": True,
            "occupation_a3_derivation": True,
        },
        "remaining": [
            "derive the variable-constants thermal frame map T_energy(a)",
            "derive active baryon density and ionization/drag history",
            "derive pre-drag H_J(a)",
        ],
    }


def variable_constants_thermal_frame_map_payload() -> dict:
    """Solve the Eq40 blackbody/adiabatic radiation exponent system."""

    hc_cubed_exponent = 3.0
    target_number_exponent = -3.0
    target_energy_density_exponent = -4.0
    theta_exponent = -1.0
    occupation_exponent = 3.0
    solved_number_exponent = occupation_exponent + 3.0 * theta_exponent - hc_cubed_exponent
    solved_energy_exponent = occupation_exponent + 4.0 * theta_exponent - hc_cubed_exponent
    return {
        "status": "janus-variable-constants-thermal-frame-map",
        "inputs": {
            "Eq40_hc_cubed_exponent": hc_cubed_exponent,
            "adiabatic_radiation_energy_density_exponent": target_energy_density_exponent,
            "conserved_comoving_photon_number_density_exponent": target_number_exponent,
        },
        "solution": {
            "thermal_energy_temperature_exponent": theta_exponent,
            "occupation_exponent": occupation_exponent,
            "n_gamma_exponent": solved_number_exponent,
            "rho_gamma_exponent": solved_energy_exponent,
        },
        "checks": {
            "number_target_matched": solved_number_exponent == target_number_exponent,
            "energy_target_matched": solved_energy_exponent == target_energy_density_exponent,
            "occupation_matches_required_a3": occupation_exponent == REQUIRED_OCCUPATION_EXPONENT,
        },
        "interpretation": (
            "In the Eq40 variable-constants frame, T_energy~a^-1 is fixed by "
            "adiabatic radiation plus conserved comoving photon number. It is "
            "paired uniquely with occupation~a^3."
        ),
        "remaining": [
            "derive the occupation factor as real entropy/phase-space degeneracy",
            "derive active baryon density",
            "derive ionization and drag visibility",
            "derive pre-drag H_J(a)",
        ],
    }


def native_drag_exponent_frontier_payload() -> dict:
    """Exponent frontier for a Janus-native drag epoch.

    With conserved baryon/electron number, Eq40 gives:
    n_e ~ a^-3, sigma_T ~ a^2, c ~ a^-1/2, hence
    Gamma_drag = n_e sigma_T c ~ a^-3/2 before ionization suppression.

    If H_J ~ a^p, then Gamma/H ~ a^(-3/2-p). A standard radiation-like
    H (p=-2 or steeper) has the wrong monotonicity: coupling is not stronger
    in the far past. A native Janus pre-drag branch must therefore derive a
    shallower H_J, a modified redshift/time map, or an ionization/visibility
    law that supplies the crossing.
    """

    gamma_exponent = -1.5
    h_candidates = {
        "standard_matter_like": -1.5,
        "standard_radiation_like": -2.0,
        "variable_G_radiation_like": -2.5,
        "constant_H_bridge_like": 0.0,
        "janus_required_boundary": -1.49,
    }
    rows = []
    for name, h_exp in h_candidates.items():
        ratio_exp = gamma_exponent - h_exp
        rows.append(
            {
                "name": name,
                "H_exponent": h_exp,
                "Gamma_over_H_exponent": ratio_exp,
                "early_coupling_stronger": ratio_exp < 0.0,
                "drag_crossing_possible_without_ionization": ratio_exp < 0.0,
            }
        )
    return {
        "status": "janus-native-drag-exponent-frontier",
        "derived_exponents": {
            "n_e": -3.0,
            "sigma_T": 2.0,
            "c": -0.5,
            "Gamma_drag": gamma_exponent,
        },
        "condition_for_standard_early_coupling": {
            "if_H_J_scales_as_a_power_p": "Gamma/H exponent = -3/2 - p",
            "required": "p > -3/2",
        },
        "candidate_H_scalings": rows,
        "bottom_line": (
            "Eq40 plus conserved baryons makes Gamma_drag~a^-3/2. "
            "A radiation-like pre-drag H_J is too steep. The next real model "
            "input must be a Janus-native H_J/redshift-time branch or an "
            "ionization visibility law; alpha fitting cannot fix this."
        ),
        "remaining": [
            "derive pre-drag H_J(a) from the bimetric/variable-constants action",
            "derive x_e(a) and visibility in the Eq40 thermal frame",
            "derive r_d^J only after H_J and c_s^J are closed",
        ],
    }


def predrag_hubble_source_exponent_matrix_payload() -> dict:
    """Classify H_J power laws from Eq40-scaled source components."""

    # H^2 source exponent q gives H exponent p=q/2.
    components = [
        {
            "name": "radiation_fluid",
            "energy_density_exponent": -4.0,
            "mass_density_exponent_after_c2": -3.0,
            "G_rho_exponent": -4.0,
            "H_exponent": -2.0,
            "drag_regime": "fails_early_coupling",
        },
        {
            "name": "conserved_matter_or_baryons",
            "energy_density_exponent": -3.0,
            "mass_density_exponent_after_c2": -2.0,
            "G_rho_exponent": -3.0,
            "H_exponent": -1.5,
            "drag_regime": "boundary_constant_ratio",
        },
        {
            "name": "curvature_like_term",
            "energy_density_exponent": None,
            "mass_density_exponent_after_c2": None,
            "G_rho_exponent": -3.0,
            "H_exponent": -1.5,
            "drag_regime": "boundary_constant_ratio",
        },
        {
            "name": "bridge_or_vacuum_state_energy",
            "energy_density_exponent": 0.0,
            "mass_density_exponent_after_c2": 1.0,
            "G_rho_exponent": 0.0,
            "H_exponent": 0.0,
            "drag_regime": "can_restore_early_coupling",
        },
    ]
    viable = [row["name"] for row in components if row["H_exponent"] > -1.5]
    return {
        "status": "janus-predrag-hubble-source-exponent-matrix",
        "rule": "Eq40: c^2~a^-1, G~a^-1; H exponent is half the Friedmann source exponent.",
        "components": components,
        "viable_for_native_drag_without_ionization": viable,
        "bottom_line": (
            "Ordinary radiation gives H~a^-2 and fails the Eq40 drag monotonicity. "
            "Matter and curvature sit exactly at Gamma/H constant. A native BAO "
            "crossing needs either an ionization visibility law or a bridge/vacuum "
            "state component that makes H_J shallower than a^-3/2."
        ),
        "next_non_rustine_targets": [
            "derive bridge/vacuum state energy from Janus/PT boundary state law",
            "derive ionization visibility from Eq40 thermal frame",
            "test whether mixed plus/minus pre-drag source can yield H exponent > -3/2",
        ],
    }


def eq40_saha_ionization_scaling_payload() -> dict:
    """Saha/recombination scaling in the Eq40 thermal frame."""

    scalings = {
        "m_e": 1.0,
        "T_energy": -1.0,
        "h": 1.5,
        "n_b": -3.0,
        "ionization_energy": 0.0,
    }
    thermal_prefactor_exponent = 1.5 * (
        scalings["m_e"] + scalings["T_energy"] - 2.0 * scalings["h"]
    )
    saha_over_nb_power = thermal_prefactor_exponent - scalings["n_b"]
    return {
        "status": "janus-eq40-saha-ionization-scaling",
        "scalings": scalings,
        "saha_form": "x_e^2/(1-x_e) proportional (m_e T/h^2)^(3/2) n_b^-1 exp(-E_ion/T)",
        "derived": {
            "thermal_prefactor_exponent": thermal_prefactor_exponent,
            "prefactor_over_baryon_exponent": saha_over_nb_power,
            "exponential_argument": "- const * a",
        },
        "interpretation": (
            "Eq40 makes E_ion constant and T_energy~a^-1, so the Saha "
            "exponential becomes exp(-const*a). The plasma is ionized at "
            "small a and recombines as a grows. This gives a native visibility "
            "mechanism even though the power-law drag ratio alone is marginal "
            "or wrong for ordinary H_J components."
        ),
        "unblocks": {
            "native_ionization_visibility_law": True,
            "drag_epoch_possible_with_xe_drop": True,
            "requires_absolute_eta_b_or_temperature_anchor": True,
        },
        "remaining": [
            "derive the dimensionless constant E_ion/T0 in Janus units",
            "derive baryon-to-photon ratio or baryon density normalization",
            "combine x_e(a), Gamma_drag(a), H_J(a) into a bracketed z_d^J",
        ],
    }


def native_drag_epoch_equation_contract_payload() -> dict:
    """Assemble the symbolic native drag crossing equation."""

    return {
        "status": "janus-native-drag-epoch-equation-contract",
        "equation": (
            "A_drag * a^(-3/2 - p_H) * x_e(a; C_ion, eta_b) = 1"
        ),
        "saha_visibility_proxy": "x_e^2/(1-x_e) = B_eta * a^-3/2 * exp(-C_ion*a)",
        "known_from_branch": {
            "Gamma_power_without_xe": "-3/2",
            "thermal_frame": "T_energy~a^-1",
            "Saha_exponential": "exp(-C_ion*a)",
            "condition_on_H_power_without_xe": "p_H > -3/2",
        },
        "remaining_inputs": {
            "C_ion": "E_ion/T0_Janus",
            "B_eta": "baryon-to-photon or baryon-density normalization",
            "A_drag": "present normalization of n_e sigma_T c / H_J",
            "p_H_or_full_HJ": "native pre-drag H_J(a)",
        },
        "numeric_prediction_ready": False,
        "structural_prediction_ready": True,
        "bottom_line": (
            "The branch has a native symbolic drag equation. It is not yet a "
            "number because C_ion, baryon normalization, and H_J(a) are not "
            "derived inside Janus. This is the exact boundary between theory "
            "extension and observational calculation."
        ),
    }


def native_sound_horizon_integral_contract_payload() -> dict:
    """Sound speed and sound-horizon convergence in the Eq40 plasma frame."""

    c_exponent = -0.5
    rb_exponent = 1.0
    h_candidates = {
        "radiation_like": -2.0,
        "matter_or_curvature_boundary": -1.5,
        "bridge_or_vacuum_shallow": 0.0,
    }
    rows = []
    for name, h_exp in h_candidates.items():
        integrand_exponent = c_exponent - 2.0 - h_exp
        finite_from_zero = integrand_exponent > -1.0
        rows.append(
            {
                "name": name,
                "H_exponent": h_exp,
                "rd_integrand_exponent_small_a": integrand_exponent,
                "finite_if_integrated_from_a0": finite_from_zero,
                "needs_nonzero_lower_limit": not finite_from_zero,
            }
        )
    return {
        "status": "janus-native-sound-horizon-integral-contract",
        "sound_speed_contract": {
            "R_b_scaling": "R_b(a)=R_b0*a",
            "c_s": "c0*a^-1/2 / sqrt(3*(1+R_b0*a))",
            "r_d_integral": "int_{a_min}^{a_d} c_s(a)/(a^2 H_J(a)) da",
        },
        "small_a_condition": {
            "if_H_J_scales_as_a_power_p": "r_d integrand exponent = -5/2 - p",
            "finite_from_zero_requires": "p < -3/2",
            "drag_early_coupling_requires": "p > -3/2 before ionization",
        },
        "candidate_H_scalings": rows,
        "janus_resolution": (
            "The drag and sound-horizon power requirements conflict if the "
            "integral starts at a=0. A Janus throat/bounce lower bound a_min>0 "
            "or a non-power transition is therefore not cosmetic: it is what "
            "can make a shallow bridge-era H_J compatible with a finite ruler."
        ),
        "remaining": [
            "derive active a_min/throat lower bound for the early plasma branch",
            "derive or reject a bridge-to-radiation transition in H_J(a)",
            "derive R_b0 or baryon/photon normalization",
            "compute r_d^J only after a_min, a_d, and H_J(a) are supplied",
        ],
    }


def exact_shape_throat_lower_bound_payload(q0: float = -0.087) -> dict:
    """Use the published exact Janus shape to evaluate the normalized throat."""

    if q0 >= 0.0:
        raise ValueError("q0 must be negative.")
    u0 = math.asinh(math.sqrt(-1.0 / (2.0 * q0)))
    cosh_u0_sq = math.cosh(u0) ** 2
    a_min_over_a0 = 1.0 / cosh_u0_sq
    z_max = cosh_u0_sq - 1.0
    return {
        "status": "janus-exact-shape-throat-lower-bound",
        "source": "M18 exact shape a(u)=alpha*cosh(u)^2 with present normalization a0=1",
        "q0": q0,
        "u0": u0,
        "a_min_over_a0": a_min_over_a0,
        "z_max": z_max,
        "consequences": {
            "nonzero_lower_bound_for_sound_horizon": True,
            "removes_a_zero_integral_divergence": True,
            "reaches_standard_drag_redshift": z_max > 100.0,
            "published_SN_branch_sufficient_for_BAO_drag": False,
        },
        "bottom_line": (
            "The published exact SN shape supplies a genuine nonzero throat "
            "lower bound, so it can regularize the sound-horizon integral. But "
            "for q0=-0.087 the branch ends at z_max~5.75, far below any "
            "pre-drag epoch. Therefore native BAO needs an additional early-time "
            "redshift/history branch, not just the late-time exact SN shape."
        ),
        "remaining": [
            "derive an early-time branch attached to the exact shape",
            "derive a modified early redshift map if the Eq40 era precedes the SN branch",
            "prove continuity/matching of a_min, H_J, c_s, and x_e across the transition",
        ],
    }


def early_redshift_map_feasibility_payload(
    q0: float = -0.087, target_redshift: float = 1000.0
) -> dict:
    """Evaluate whether candidate early redshift maps can reach pre-drag."""

    throat = exact_shape_throat_lower_bound_payload(q0)
    a_min = throat["a_min_over_a0"]
    required_exponent = math.log1p(target_redshift) / math.log(1.0 / a_min)
    candidates = [
        {
            "name": "published_M18_geometric_redshift",
            "exponent_s": 1.0,
            "status": "paper_native_late_time",
            "derived": True,
        },
        {
            "name": "Eq40_clock_frequency_unit",
            "exponent_s": 1.5,
            "status": "plausible_unit_map_but_insufficient",
            "derived": False,
        },
        {
            "name": "Eq40_phase_space_occupation_volume",
            "exponent_s": 3.0,
            "status": "matches_a3_occupation_but_insufficient_for_z1000",
            "derived": False,
        },
        {
            "name": "four_volume_or_action_phase_map",
            "exponent_s": 4.0,
            "status": "reaches_target_but_speculative",
            "derived": False,
        },
    ]
    rows = []
    for candidate in candidates:
        z_max = a_min ** (-candidate["exponent_s"]) - 1.0
        rows.append(
            {
                **candidate,
                "z_max": z_max,
                "reaches_target": z_max >= target_redshift,
            }
        )
    return {
        "status": "janus-early-redshift-map-feasibility",
        "q0": q0,
        "a_min_over_a0": a_min,
        "target_redshift": target_redshift,
        "required_exponent_s": required_exponent,
        "candidate_maps": rows,
        "bottom_line": (
            "With the published q0=-0.087 throat, a redshift law "
            "1+z=(a0/a)^s must have s around 3.62 to reach z~1000. "
            "The paper-native geometric map and simple Eq40 clock maps fail. "
            "A four-volume/action-phase-like map could reach it, but is not "
            "derived and must not be promoted without a real photon/clock "
            "transport proof."
        ),
        "remaining": [
            "derive or reject an early photon frequency transport law with s>=required",
            "derive an early branch with smaller a_min if s remains <=3",
            "keep M18 geometric redshift as late-time only unless source proves otherwise",
        ],
    }


def redshift_exponent_q0_compatibility_payload(
    target_redshift: float = 1000.0,
    published_q0: float = -0.087,
    published_sigma: float = 0.015,
) -> dict:
    """Invert the redshift exponent map to the q0 required for pre-drag reach."""

    candidates = [
        ("geometric_s1", 1.0),
        ("clock_s3_over_2", 1.5),
        ("occupation_volume_s3", 3.0),
        ("four_volume_phase_s4", 4.0),
    ]
    rows = []
    for name, exponent in candidates:
        geometric_zmax_needed = (1.0 + target_redshift) ** (1.0 / exponent) - 1.0
        required_q0 = -1.0 / (2.0 * geometric_zmax_needed)
        sigma_offset = abs(required_q0 - published_q0) / published_sigma
        rows.append(
            {
                "name": name,
                "redshift_exponent_s": exponent,
                "required_geometric_zmax": geometric_zmax_needed,
                "required_q0": required_q0,
                "sigma_offset_from_published_q0": sigma_offset,
                "within_two_sigma": sigma_offset <= 2.0,
            }
        )
    return {
        "status": "janus-redshift-exponent-q0-compatibility",
        "target_redshift": target_redshift,
        "published_q0": published_q0,
        "published_sigma": published_sigma,
        "rows": rows,
        "bottom_line": (
            "Keeping the published q0 while reaching pre-drag redshift strongly "
            "favours a high-power early redshift map. s=1 or 3/2 forces q0 "
            "near zero. s=3 is closer but outside the quoted q0 band. s=4 is "
            "the only tested map close to the published q0 range, but it is "
            "also the least derived and therefore only a target for a real "
            "photon/clock transport law."
        ),
        "remaining": [
            "derive or rule out the s=4 action/phase redshift map",
            "if s<=3, accept that q0 must move away from the published SN value",
            "test SN+BAO only after the redshift map is source-derived",
        ],
    }


def four_power_redshift_transport_obstruction_payload() -> dict:
    """Audit whether the s=4 early redshift map can be source-derived."""

    candidate_decompositions = [
        {
            "name": "geometric_redshift_plus_occupation_volume",
            "exponent_sum": 4.0,
            "pieces": "1 + 3",
            "verdict": "invalid_as_redshift",
            "reason": "occupation/entropy changes intensity or number density, not photon frequency by itself",
        },
        {
            "name": "four_volume_phase",
            "exponent_sum": 4.0,
            "pieces": "spacetime volume scaling",
            "verdict": "unproved",
            "reason": "requires an action-phase transport law mapping four-volume phase to observed spectral redshift",
        },
        {
            "name": "clock_time_plus_hc_length",
            "exponent_sum": 2.5,
            "pieces": "3/2 + 1",
            "verdict": "insufficient",
            "reason": "uses Eq40 unit scalings but does not reach s=4",
        },
    ]
    return {
        "status": "janus-four-power-redshift-transport-obstruction",
        "required_for_pre_drag_with_published_q0": "s around 3.62; s=4 works numerically",
        "candidate_decompositions": candidate_decompositions,
        "accepted_redshift_sources": [
            "photon four-momentum transport k_mu u^mu",
            "atomic clock/transition frequency at emission and observation",
            "explicit variable-constants radiative transfer law",
        ],
        "result": {
            "s4_numerically_useful": True,
            "s4_source_derived": False,
            "s4_promotable": False,
        },
        "bottom_line": (
            "The s=4 map is numerically attractive because it keeps q0 near the "
            "published SN value while reaching pre-drag redshift. But every "
            "simple decomposition found either mixes density/occupation into a "
            "frequency observable or requires an unproved action-phase transport "
            "law. It remains a target, not a model component."
        ),
        "next_required": [
            "derive photon k_mu u^mu transport through the Eq40 era",
            "derive atomic transition frequency map in the same frame",
            "prove their ratio gives s>=3.62, or reject high-power redshift",
        ],
    }


def eq40_photon_clock_transport_audit_payload() -> dict:
    """Audit spectral redshift from null transport plus Eq40 atomic clocks."""

    photon_geometric_frequency_exponent = -1.0
    atomic_transition_frequency_exponent = -1.5
    observed_photon_from_emitted_atom_exponent = (
        atomic_transition_frequency_exponent - photon_geometric_frequency_exponent
    )
    inferred_one_plus_z_exponent = -observed_photon_from_emitted_atom_exponent
    return {
        "status": "janus-eq40-photon-clock-transport-audit",
        "assumptions": {
            "flrw_null_transport": "photon frequency redshifts geometrically as a^-1",
            "Eq40_ionization_energy": "E_ion invariant",
            "Eq40_planck_constant": "h~a^3/2",
            "atomic_transition_frequency": "nu_atom~E_ion/h~a^-3/2",
        },
        "derived_exponents": {
            "photon_geometric_frequency": photon_geometric_frequency_exponent,
            "atomic_transition_frequency": atomic_transition_frequency_exponent,
            "observed_photon_frequency_from_emitted_atom": observed_photon_from_emitted_atom_exponent,
            "inferred_one_plus_z": inferred_one_plus_z_exponent,
        },
        "result": {
            "produces_high_power_redshift": inferred_one_plus_z_exponent >= 3.62,
            "produces_positive_geometric_like_redshift": inferred_one_plus_z_exponent > 0.0,
            "supports_s4": False,
            "diagnostic_only": True,
        },
        "bottom_line": (
            "Under the minimal FLRW null-transport plus Eq40 atomic-clock audit, "
            "a photon emitted by an Eq40 atomic transition does not generate the "
            "needed high-power redshift. The inferred exponent is +1/2 for "
            "1+z relative to current atomic units under this convention, not "
            "s>=3.62. Therefore s=4 is not obtained by the standard photon-clock "
            "route."
        ),
        "remaining": [
            "check whether the Janus source defines redshift geometrically instead of spectroscopically in the Eq40 era",
            "derive a nonstandard radiative transfer law if s>=3.62 is still desired",
            "keep this audit diagnostic until conventions are fixed from source/action",
        ],
    }


def early_branch_attachment_requirements_payload(target_redshift: float = 1000.0) -> dict:
    """Requirements for an attached early branch if redshift remains geometric."""

    late = exact_shape_throat_lower_bound_payload()
    required_amin = 1.0 / (1.0 + target_redshift)
    ratio = late["a_min_over_a0"] / required_amin
    return {
        "status": "janus-early-branch-attachment-requirements",
        "target_redshift": target_redshift,
        "late_SN_branch": {
            "a_min_over_a0": late["a_min_over_a0"],
            "z_max": late["z_max"],
        },
        "geometric_redshift_requirement": {
            "required_a_min_over_a0": required_amin,
            "late_branch_a_min_too_large_by_factor": ratio,
        },
        "required_new_structure": [
            "early Eq40/pre-drag branch with a_min/a0 <= required_a_min",
            "matching surface from early branch to published late SN branch",
            "continuity of a, H_J, photon clock/redshift map, c_s, x_e",
            "no refit of late q0 unless declared as new observational branch",
        ],
        "result": {
            "published_late_branch_can_be_reused_alone": False,
            "separate_early_branch_required_if_s4_rejected": True,
            "new_integration_constant_or_state_law_required": True,
        },
        "bottom_line": (
            "If high-power redshift is rejected, native BAO requires a separate "
            "early branch. The late published throat has a_min/a0~0.148, while "
            "geometric pre-drag reach needs a_min/a0~0.001. This is not a "
            "small correction; it is a new early-history layer that must be "
            "matched to the SN branch."
        ),
    }


def early_universe_native_plasma_frontier_verdict_payload() -> dict:
    """Current frontier for the Janus native early-plasma/BAO branch."""

    return {
        "status": "janus-early-universe-native-plasma-frontier-verdict",
        "closed": [
            "Eq40 microphysics scalings",
            "plus-sector Maxwell/radiation extension contract",
            "conditional Noether photon-stress conservation within extension",
            "adiabatic radiation first-law exponent system",
            "thermal frame T_energy~a^-1 paired with occupation~a^3",
            "Eq40 Saha visibility scaling",
            "symbolic drag crossing equation",
            "native sound-speed and sound-horizon contract",
            "published exact-shape throat lower bound",
            "redshift exponent/q0 feasibility matrix",
            "C1 attached early-branch diagnostic",
            "C1 early-branch time-scale ratio law after inputs",
            "a_min integer-sector requirements",
            "boundary Hilbert requirements: N=1001, CP1 j=500, KKS/CS k=1000",
            "boundary state-law candidate matrix including 1001=C(14,4)",
            "M31 symmetric-power candidate: dim Sym^4(C^11)=1001",
            "dimension-to-a_min map audit: only linear map reaches z~1000",
        ],
        "blocked": [
            "numeric z_d^J and r_d^J",
            "absolute C_ion=E_ion/T0_Janus",
            "baryon/photon normalization",
            "drag normalization A_drag",
            "full native pre-drag H_J(a)",
            "source-derived high-power early redshift map",
            "attached early-time branch and matching surface",
            "source law selecting early a_min or integer N",
            "Janus/PT boundary state law selecting N=1001 without BAO input",
            "map from boundary Hilbert sector to a_min and photon/ruler dynamics",
            "linear-resolution law a_min=1/N from Sym^4(C^11)",
        ],
        "surviving_routes": [
            {
                "route": "derive_high_power_photon_clock_transport",
                "needed": "prove a spectral redshift exponent s>=3.62 from photon/clock transport",
                "status": "currently obstructed; s=4 useful but not derived",
            },
            {
                "route": "derive_attached_early_branch",
                "needed": "early a_min/a0 around 0.001 plus matching to late SN branch",
                "status": "C1 time-scale fixed after inputs; needs a_min/N selection law",
            },
            {
                "route": "derive_boundary_state_law_for_N",
                "needed": "derive Sym^4(C^11) boundary statistics and linear map a_min=1/N",
                "status": "best structural candidate; needs boundary state and resolution law",
            },
        ],
        "not_allowed": [
            "import Lambda-CDM r_d",
            "fit alpha to hide the redshift/drag mismatch",
            "multiply redshift by occupation factor",
            "claim BAO prediction before H_J, x_e, a_d, and r_d are numeric",
        ],
        "bottom_line": (
            "The branch advanced from vague BAO failure to a sharp frontier. "
            "Eq40 can support native microphysics and Saha visibility, but the "
            "published late SN branch cannot by itself reach pre-drag redshift. "
            "A real solution needs either a derived high-power photon/clock "
            "transport law or a separate matched early-time branch. The latter "
            "has now been reduced to a boundary state-law problem. The cleanest "
            "candidate is Sym^4(C^11). It gives N=1001 cleanly, but BAO reach "
            "requires N to count linear throat/redshift resolution states."
        ),
    }


def attached_early_branch_c1_diagnostic_payload(
    q0: float = -0.087, transition_redshift: float = 5.0, target_redshift: float = 1000.0
) -> dict:
    """Construct a minimal C1 early-branch attachment diagnostic."""

    if q0 >= 0.0:
        raise ValueError("q0 must be negative.")
    u0 = math.asinh(math.sqrt(-1.0 / (2.0 * q0)))

    def h_shape(u: float) -> float:
        return math.sinh(2.0 * u) / (math.cosh(u) ** 4)

    cosh_u0_sq = math.cosh(u0) ** 2
    a_transition = 1.0 / (1.0 + transition_redshift)
    u_transition = math.acosh(math.sqrt(cosh_u0_sq * a_transition))
    h_late_transition = h_shape(u_transition) / h_shape(u0)
    a_min_early = 1.0 / (1.0 + target_redshift)
    y_transition = math.acosh(math.sqrt(a_transition / a_min_early))
    early_shape_h = h_shape(y_transition)
    early_time_scale_ratio = h_late_transition / early_shape_h
    return {
        "status": "janus-attached-early-branch-c1-diagnostic",
        "inputs": {
            "q0": q0,
            "transition_redshift": transition_redshift,
            "target_redshift": target_redshift,
        },
        "late_branch_at_transition": {
            "a_transition": a_transition,
            "u_transition": u_transition,
            "H_over_H0": h_late_transition,
        },
        "early_branch": {
            "form": "a_E(y)=a_min_E*cosh(y)^2",
            "a_min_E": a_min_early,
            "y_transition": y_transition,
            "time_scale_ratio_needed": early_time_scale_ratio,
        },
        "result": {
            "C0_match_possible": True,
            "C1_H_match_possible": early_time_scale_ratio > 0.0,
            "requires_new_time_scale_or_state_constant": True,
            "source_derived": False,
            "physical_model_ready": False,
        },
        "bottom_line": (
            "A smooth C1 geometric attachment is possible in principle: an "
            "early cosh-type branch with a_min~1/1001 can match the late SN "
            "branch at z=5 by choosing a new time-scale ratio. But that ratio "
            "is a new state/integration constant until derived from the action "
            "or a boundary law."
        ),
    }


def attached_early_branch_timescale_law_payload(
    q0: float = -0.087, transition_redshift: float = 5.0, target_redshift: float = 1000.0
) -> dict:
    """Exact C1 time-scale law for the attached cosh early branch."""

    diag = attached_early_branch_c1_diagnostic_payload(q0, transition_redshift, target_redshift)
    a_transition = diag["late_branch_at_transition"]["a_transition"]
    h_late = diag["late_branch_at_transition"]["H_over_H0"]
    a_min = diag["early_branch"]["a_min_E"]
    x = a_transition / a_min
    exact_h_shape = 2.0 * math.sqrt(x - 1.0) / (x ** 1.5)
    exact_ratio = h_late / exact_h_shape
    asymptotic_ratio = 0.5 * h_late * x
    return {
        "status": "janus-attached-early-branch-timescale-law",
        "inputs": {
            "q0": q0,
            "transition_redshift": transition_redshift,
            "target_redshift": target_redshift,
            "x_equals_a_transition_over_a_min": x,
        },
        "law": {
            "early_h_shape_exact": "2*sqrt(x-1)/x^(3/2)",
            "time_scale_ratio_exact": "H_late/H0 divided by early_h_shape_exact",
            "large_x_asymptotic": "(H_late/H0)*x/2",
        },
        "values": {
            "exact_time_scale_ratio": exact_ratio,
            "diagnostic_time_scale_ratio": diag["early_branch"]["time_scale_ratio_needed"],
            "large_x_asymptotic_ratio": asymptotic_ratio,
            "relative_asymptotic_error": abs(exact_ratio - asymptotic_ratio) / exact_ratio,
        },
        "result": {
            "time_scale_ratio_geometrically_fixed_after_inputs": True,
            "new_free_ratio_removed": True,
            "a_min_selection_still_open": True,
            "transition_selection_still_open": True,
            "physical_model_ready": False,
        },
        "bottom_line": (
            "The C1 time-scale ratio is not an independent fit parameter once "
            "a_min and the matching redshift are specified. It is fixed by the "
            "cosh-branch shape. The remaining non-rustine problem is selecting "
            "a_min and the transition from Janus physics."
        ),
    }


def amin_selection_candidate_matrix_payload(target_redshift: float = 1000.0) -> dict:
    """Evaluate candidate non-fit selectors for the early-branch a_min."""

    required = 1.0 / (1.0 + target_redshift)
    candidates = [
        {
            "name": "drag_reach_definition",
            "a_min": required,
            "status": "circular",
            "reason": "sets a_min by the desired BAO target redshift",
        },
        {
            "name": "Eq40_length_unit_ratio",
            "a_min": None,
            "status": "underdetermined",
            "reason": "Eq40 says characteristic lengths scale as a, but gives no absolute early cutoff",
        },
        {
            "name": "Saha_half_ionization_condition",
            "a_min": None,
            "status": "requires_C_ion_and_eta_b",
            "reason": "visibility can select a_d, not a_min, once constants are known",
        },
        {
            "name": "Planck_or_quantum_length_cutoff",
            "a_min": None,
            "status": "new_quantum_gravity_input",
            "reason": "would be physically meaningful but not derived from current Janus action",
        },
        {
            "name": "topological_integer_sector",
            "a_min": "1/N",
            "status": "open_if_N_derived",
            "reason": "N~1000 would work, but no Janus theorem fixes N",
        },
        {
            "name": "published_late_SN_throat",
            "a_min": exact_shape_throat_lower_bound_payload()["a_min_over_a0"],
            "status": "fails_predrag",
            "reason": "too large by about 148 for geometric z~1000",
        },
    ]
    return {
        "status": "janus-amin-selection-candidate-matrix",
        "required_a_min_for_geometric_z_target": required,
        "candidates": candidates,
        "bottom_line": (
            "No current non-rustine selector fixes the early a_min near 1/1000. "
            "Saha selects a drag surface after constants are supplied, not the "
            "branch throat. A topological/quantum sector could do it only if a "
            "Janus law derives N."
        ),
        "next_required": [
            "derive a topological integer/sector law for N, or reject this route",
            "derive a quantum-gravity cutoff from the Janus action, or reject this route",
            "otherwise treat early a_min as a new state parameter and test observationally",
        ],
    }


def amin_integer_sector_requirements_payload(target_redshift: float = 1000.0) -> dict:
    """Requirements if the early throat is selected by a_min=1/N."""

    required_n = int(math.ceil(1.0 + target_redshift))
    candidates = [
        {
            "name": "covering_degree",
            "N": 2,
            "status": "fails",
            "reason": "Janus projective cover gives 2, not ~1000",
        },
        {
            "name": "CMB_drag_target_integer",
            "N": required_n,
            "status": "circular_if_chosen_for_z",
            "reason": "works only by identifying N with the desired redshift reach",
        },
        {
            "name": "large_boundary_hilbert_dimension",
            "N": required_n,
            "status": "possible_but_needs_state_law",
            "reason": "would need Janus to derive a finite boundary Hilbert-sector dimension",
        },
        {
            "name": "flux_or_area_quantization",
            "N": required_n,
            "status": "possible_but_needs_charge_unit",
            "reason": "requires a derived flux unit or area gap on the early throat",
        },
    ]
    return {
        "status": "janus-amin-integer-sector-requirements",
        "ansatz": "a_min,E = 1/N",
        "target_redshift": target_redshift,
        "required_N_min": required_n,
        "candidates": candidates,
        "internal_tests_required": [
            "N derived without using BAO target",
            "N stable under late-branch q0 uncertainty",
            "N enters photon/ruler dynamics, not only topology label",
            "N compatible with 2-fold projective cover rather than replacing it",
        ],
        "bottom_line": (
            "An integer sector N~1001 would make the early branch reach z~1000 "
            "with geometric redshift. But Janus topology currently gives only "
            "the 2-fold projective cover. A large N needs a new boundary Hilbert, "
            "flux, area, or state-count law."
        ),
    }


def boundary_hilbert_N_selector_requirements_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Requirements for selecting early a_min from a boundary Hilbert sector."""

    required_n = int(math.ceil(1.0 + target_redshift))
    spin_j = (required_n - 1.0) / 2.0
    kks_level = int(2.0 * spin_j)
    candidates = [
        {
            "name": "CP1_spin_j_orbit",
            "dimension_formula": "N=2j+1",
            "required_value": f"j={spin_j}",
            "mathematically_valid": True,
            "janus_derived": False,
            "blocker": "requires Janus/PT sector law selecting j=500",
        },
        {
            "name": "KKS_prequantization_level",
            "dimension_formula": "N=k+1",
            "required_value": f"k={kks_level}",
            "mathematically_valid": True,
            "janus_derived": False,
            "blocker": "requires nonzero KKS cycle plus level selection k=1000",
        },
        {
            "name": "SU2_boundary_spin_network_punctures",
            "dimension_formula": "N as puncture/state count",
            "required_value": f"N={required_n}",
            "mathematically_valid": True,
            "janus_derived": False,
            "blocker": "requires throat puncture law and area/flux unit",
        },
    ]
    return {
        "status": "janus-boundary-hilbert-N-selector-requirements",
        "target_redshift": target_redshift,
        "required_N": required_n,
        "required_CP1_spin_j": spin_j,
        "required_KKS_or_CS_level": kks_level,
        "candidates": candidates,
        "existing_repo_anchor": {
            "CP1_candidate_exists": True,
            "KKS_symbolic_period_exists": True,
            "prequantization_integrality_scaffold_exists": True,
            "sector_selection_law_derived": False,
        },
        "bottom_line": (
            "A boundary Hilbert route is mathematically clean: CP1 spin j=500 "
            "or KKS/CS level k=1000 would give N=1001. The repo already has "
            "CP1/KKS scaffolding, but it does not derive the global Janus/PT "
            "sector selection law that fixes j or k. This is the next hard "
            "quantum-frontier target, not a numerical fit."
        ),
        "next_required": [
            "derive global Janus/PT CP1 from the resolved throat, not only local spinors",
            "derive a compact KKS two-cycle with nonzero period",
            "derive sector selection j=500 or k=1000 without BAO input",
            "prove N enters a_min and photon/ruler dynamics",
        ],
    }


def boundary_hilbert_sector_selection_frontier_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Audit whether any current boundary-Hilbert route selects N non-circularly."""

    req = boundary_hilbert_N_selector_requirements_payload(target_redshift)
    required_n = req["required_N"]
    spin_j = req["required_CP1_spin_j"]
    kks_level = req["required_KKS_or_CS_level"]
    routes = [
        {
            "name": "projective_cover_degree",
            "candidate_N": 2,
            "can_reach_required_N": False,
            "non_circular_selector_available": True,
            "blocked_by": "S4/RP4 and Z2 throat topology select the cover degree 2, not a large Hilbert-sector dimension",
        },
        {
            "name": "global_CP1_spinor_orbit",
            "candidate_N": required_n,
            "required_sector": f"spin j={spin_j}",
            "can_reach_required_N": True,
            "non_circular_selector_available": False,
            "blocked_by": (
                "local CP1 exists, but global Z2/Sigma spinor projection, resolved Pin lift, "
                "plus/minus spinor bundle data, and j-sector selection are not derived"
            ),
        },
        {
            "name": "KKS_prequantization_level",
            "candidate_N": required_n,
            "required_sector": f"level k={kks_level}",
            "can_reach_required_N": True,
            "non_circular_selector_available": False,
            "blocked_by": (
                "symbolic KKS period exists, but compact nonzero Janus/PT two-cycle, "
                "aroundSigma action on CP1, and level-selection law are not derived"
            ),
        },
        {
            "name": "CS_or_U1_flux_level",
            "candidate_N": required_n,
            "required_sector": f"primitive flux/level {kks_level}",
            "can_reach_required_N": True,
            "non_circular_selector_available": False,
            "blocked_by": "requires a boundary gauge action, charge unit, and primitive flux sector derived from Janus/PT",
        },
        {
            "name": "spin_network_or_area_punctures",
            "candidate_N": required_n,
            "required_sector": f"{required_n} effective states or punctures",
            "can_reach_required_N": True,
            "non_circular_selector_available": False,
            "blocked_by": "requires an area gap or puncture-count law and a map from area states to a_min",
        },
    ]
    non_circular_successes = [
        row["name"]
        for row in routes
        if row["can_reach_required_N"] and row["non_circular_selector_available"]
    ]
    return {
        "status": "janus-boundary-hilbert-sector-selection-frontier",
        "target_redshift": target_redshift,
        "required_N": required_n,
        "required_CP1_spin_j": spin_j,
        "required_KKS_or_CS_level": kks_level,
        "routes": routes,
        "non_circular_successes": non_circular_successes,
        "sector_selection_no_fit_ready": bool(non_circular_successes),
        "current_branch_verdict": (
            "blocked_without_boundary_state_law"
            if not non_circular_successes
            else "boundary_sector_selector_available"
        ),
        "hard_frontier": [
            "derive global Janus/PT spinor bundle data selecting j",
            "derive compact nonzero KKS two-cycle plus level selection",
            "derive boundary gauge/flux primitive sector",
            "derive area or puncture law mapped to a_min",
        ],
        "bottom_line": (
            "The current branch can say exactly which sector would be needed "
            f"(N={required_n}, CP1 j={spin_j}, KKS/CS k={kks_level}), but none "
            "of the existing Janus/PT objects selects that sector without either "
            "using the BAO target or adding a new boundary state law."
        ),
    }


def boundary_state_law_candidate_matrix_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Candidate boundary state laws that could non-circularly select N."""

    required_n = int(math.ceil(1.0 + target_redshift))
    jan_lie_dimension = 11
    cpt_independent_generators = 3
    exterior_n = jan_lie_dimension + cpt_independent_generators
    exterior_k = 4
    exterior_dim = math.comb(exterior_n, exterior_k)
    candidates = [
        {
            "name": "CP1_spin_superselection",
            "selector": "choose an irreducible CP1/SU2 spin sector",
            "target_match": "j=500 gives N=2j+1=1001",
            "physical_meaning": "the throat boundary carries one large global spin/coadjoint-orbit sector",
            "derived_from_current_janus": False,
            "missing": "global Janus/PT spin bundle plus sector-selection law for j",
        },
        {
            "name": "KKS_or_CS_level_selection",
            "selector": "prequantized KKS or Chern-Simons level",
            "target_match": "k=1000 gives N=k+1=1001",
            "physical_meaning": "the throat boundary is a compact quantum phase space with fixed topological level",
            "derived_from_current_janus": False,
            "missing": "nonzero compact two-cycle, boundary action, and level quantization from Janus/PT",
        },
        {
            "name": "flux_or_area_puncture_count",
            "selector": "primitive boundary flux or spin-network area sector",
            "target_match": "1001 effective punctures/states",
            "physical_meaning": "the early throat size is a count of elementary flux/area cells",
            "derived_from_current_janus": False,
            "missing": "area gap, flux unit, and map from cells to a_min",
        },
        {
            "name": "symmetric_power_boundary_boson_sector",
            "selector": "dimension of Sym^4(C^11)",
            "target_match": "C(11+4-1,4)=C(14,4)=1001",
            "physical_meaning": (
                "the boundary state is a homogeneous degree-4 bosonic/Fock sector "
                "over the eleven M31 Janus torsor modes"
            ),
            "derived_from_current_janus": False,
            "missing": "boundary bosonic statistics, degree-4 constraint, and map from Sym^4 sector to a_min",
        },
        {
            "name": "exterior_power_boundary_fermion_sector",
            "selector": "dimension of Lambda^4(C^14)",
            "target_match": f"C({exterior_n},{exterior_k})={exterior_dim}",
            "physical_meaning": (
                "the boundary state is a four-excitation fermionic sector over "
                "eleven Janus torsor/Lie modes plus three CPT generators"
            ),
            "derived_from_current_janus": False,
            "missing": "boundary exterior-algebra Hilbert law and map from Lambda^4 sector to a_min",
        },
        {
            "name": "anomaly_or_modular_consistency_level",
            "selector": "level fixed by anomaly cancellation/modular invariance",
            "target_match": "could select k=1000 only if the anomaly polynomial demands it",
            "physical_meaning": "the allowed universe sector is fixed by consistency of the boundary quantum theory",
            "derived_from_current_janus": False,
            "missing": "boundary field content, anomaly polynomial, and modular constraint",
        },
        {
            "name": "microcanonical_boundary_entropy_peak",
            "selector": "N selected by extremizing boundary entropy/free energy",
            "target_match": "could prefer N~1001 only with a derived Hamiltonian and measure",
            "physical_meaning": "our sector is the dominant boundary state, not a freely chosen one",
            "derived_from_current_janus": False,
            "missing": "boundary Hamiltonian, temperature/constraint ensemble, and measure",
        },
    ]
    viable_not_derived = [
        row["name"] for row in candidates if not row["derived_from_current_janus"]
    ]
    return {
        "status": "janus-boundary-state-law-candidate-matrix",
        "target_redshift": target_redshift,
        "required_N": required_n,
        "number_theory": {
            "factorization": "1001 = 7 * 11 * 13",
            "binomial_identity": "1001 = C(14,4) = C(14,10)",
            "exterior_power_candidate_matches": exterior_dim == required_n,
            "symmetric_power_C11_candidate_matches": math.comb(jan_lie_dimension + exterior_k - 1, exterior_k) == required_n,
            "M31_janus_lie_dimension": jan_lie_dimension,
            "M31_independent_CPT_generators": cpt_independent_generators,
            "M31_spacetime_translation_dimension": exterior_k,
            "M31_stress_energy_vector_dimension": exterior_k,
            "M31_count_candidate_for_14_modes": True,
            "current_janus_source_anchor_for_14_modes": True,
            "current_janus_source_anchor_for_degree_4": True,
            "current_janus_source_anchor_for_exterior_power_law": False,
        },
        "candidates": candidates,
        "current_acceptance": {
            "accepted_as_no_fit_law": [],
            "viable_but_not_derived": viable_not_derived,
            "requires_new_boundary_state_law": True,
            "best_current_candidate": "symmetric_power_boundary_boson_sector",
        },
        "bottom_line": (
            "There are several mathematically natural ways to get a 1001-dimensional "
            "boundary sector. The cleanest current candidate is Sym^4(C^11): it "
            "uses the published M31 Janus Lie/torsor dimension 11 and the R4 "
            "translation/stress-energy degree 4, without treating discrete CPT "
            "labels as modes. It still does not derive the boundary statistics "
            "or the Sym^4-to-a_min map."
        ),
    }


def m31_torsor_cpt_exterior_power_candidate_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Deep audit of the M31-derived 11+3 -> C(14,4) candidate."""

    required_n = int(math.ceil(1.0 + target_redshift))
    jan_lie_dimension = 11
    cpt_independent_generators = 3
    primitive_modes = jan_lie_dimension + cpt_independent_generators
    exterior_degree = 4
    exterior_dimension = math.comb(primitive_modes, exterior_degree)
    degree_spectrum = [
        {
            "degree": degree,
            "dimension": math.comb(primitive_modes, degree),
            "matches_required_N": math.comb(primitive_modes, degree) == required_n,
        }
        for degree in range(primitive_modes + 1)
    ]
    return {
        "status": "janus-m31-torsor-cpt-exterior-power-candidate",
        "source_anchor": "M31 Janus symplectic group",
        "published_inputs": {
            "Janus_Lie_group_dimension": jan_lie_dimension,
            "torsor_components": "ell(3), g(3), p(3), E(1), q(1)",
            "CPT_independent_Z2_generators": cpt_independent_generators,
            "CPT_generators": ["C", "P", "T"],
            "spacetime_translation_dimension": exterior_degree,
            "stress_energy_vector_dimension": exterior_degree,
        },
        "candidate_construction": {
            "primitive_boundary_mode_count": primitive_modes,
            "exterior_degree": exterior_degree,
            "sector_dimension": exterior_dimension,
            "matches_required_N": exterior_dimension == required_n,
            "formula": "dim Lambda^4(C^(11+3)) = C(14,4) = 1001",
            "matching_exterior_degrees": [
                row["degree"] for row in degree_spectrum if row["matches_required_N"]
            ],
            "degree_4_preferred_over_degree_10_reason": (
                "degree 4 matches the M31 R4 translation/stress-energy sector; "
                "degree 10 is the Hodge-dual complement and has no separate current anchor"
            ),
        },
        "degree_spectrum": degree_spectrum,
        "why_not_closed": {
            "mixes_continuous_torsor_modes_and_discrete_CPT_generators": True,
            "boundary_fermionic_exterior_algebra_derived": False,
            "four_excitation_sector_selected": False,
            "exterior_power_statistics_derived": False,
            "sector_maps_to_a_min": False,
            "sector_maps_to_photon_ruler_dynamics": False,
        },
        "non_rustine_next_step": (
            "derive a boundary Hilbert construction where M31 torsor components "
            "and CPT generators become primitive boundary modes, then prove "
            "that the R4 translation/stress-energy structure induces a Lambda^4 "
            "exterior sector with physical boundary statistics"
        ),
        "verdict": "best_current_numerical_coincidence_but_not_a_derivation",
    }


def m31_exterior_power_consistency_audit_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Check whether the M31 11+3 exterior-power count is structurally legal."""

    required_n = int(math.ceil(1.0 + target_redshift))
    lie_modes = 11
    cpt_generators = 3
    additive_modes = lie_modes + cpt_generators
    additive_dim = math.comb(additive_modes, 4)
    sector_factor_dim = (2 ** cpt_generators) * math.comb(lie_modes, 4)
    cpt_clifford_spinor_dim = 2 ** (cpt_generators // 2)
    clifford_factor_dim = cpt_clifford_spinor_dim * math.comb(lie_modes, 4)
    alternatives = [
        {
            "name": "additive_CPT_as_fermionic_modes",
            "dimension": additive_dim,
            "matches_required_N": additive_dim == required_n,
            "structurally_legal_from_M31": False,
            "reason": "C,P,T are discrete components, not infinitesimal one-particle modes in M31",
        },
        {
            "name": "CPT_as_superselection_factor",
            "dimension": sector_factor_dim,
            "matches_required_N": sector_factor_dim == required_n,
            "structurally_legal_from_M31": True,
            "reason": "three independent Z2 labels naturally give eight sectors multiplying the continuous torsor construction",
        },
        {
            "name": "CPT_as_real_clifford_spinor_factor",
            "dimension": clifford_factor_dim,
            "matches_required_N": clifford_factor_dim == required_n,
            "structurally_legal_from_M31": False,
            "reason": "requires an extra Clifford/spin boundary representation not present in M31",
        },
        {
            "name": "pure_torsor_exterior_degree_4",
            "dimension": math.comb(lie_modes, 4),
            "matches_required_N": math.comb(lie_modes, 4) == required_n,
            "structurally_legal_from_M31": True,
            "reason": "uses only the 11-dimensional Janus Lie/torsor sector",
        },
    ]
    legal_matches = [
        row["name"]
        for row in alternatives
        if row["matches_required_N"] and row["structurally_legal_from_M31"]
    ]
    return {
        "status": "janus-m31-exterior-power-consistency-audit",
        "required_N": required_n,
        "alternatives": alternatives,
        "legal_matches": legal_matches,
        "additive_11_plus_3_match_is_structurally_suspect": additive_dim == required_n,
        "current_no_fit_selector_survives_audit": bool(legal_matches),
        "bottom_line": (
            "The 11+3 count is numerically strong but structurally suspect: M31 "
            "treats C,P,T as discrete connected-component labels, not continuous "
            "boundary modes. The structurally legal M31 readings give C(11,4)=330 "
            "or 8*C(11,4)=2640, not 1001. To keep C(14,4), one must derive a new "
            "boundary fermionization/Clifford lift that turns CPT labels into "
            "three physical one-particle modes."
        ),
        "next_required": [
            "derive CPT boundary fermionization or reject C(14,4)",
            "derive an alternative legal M31 sector matching observations",
            "if none, keep N observational/state-sector rather than no-fit",
        ],
    }


def cpt_boundary_fermionization_frontier_payload() -> dict:
    """Audit the exact missing theorem for turning CPT labels into modes."""

    inputs = {
        "resolved_tunnel_Pin_lift_ready": True,
        "Z2Sigma_spinor_projection_ready": True,
        "unit_normal_Clifford_action_ready": True,
        "projected_charge_reduction_ready": True,
        "global_fermion_occupation_number_fixed": False,
    }
    requirements = {
        "three_CPT_operators_on_boundary_Hilbert_space": False,
        "operators_are_CAR_or_Clifford_generators": False,
        "C_operator_as_internal_charge_conjugation_mode": False,
        "P_T_operators_as_independent_boundary_modes": False,
        "CPT_modes_are_occupiable_not_only_sector_labels": False,
        "fermionic_Fock_or_exterior_statistics_derived": False,
        "Lambda4_sector_selected": False,
    }
    partial_support = {
        "Pin_lift_supports_geometric_reflections": True,
        "normal_Clifford_action_supports_boundary_projectors": True,
        "projected_charge_reduction_identifies_open_N_occ": True,
    }
    blockers = [
        "C is internal charge conjugation, not supplied by the geometric Pin lift",
        "P and T are discrete component actions unless promoted to boundary operators",
        "normal Clifford reflection is a projector ingredient, not an occupiable mode",
        "N_occ remains open in the projected charge reduction",
        "no CAR/Fock/exterior-power boundary action is derived",
    ]
    return {
        "status": "janus-cpt-boundary-fermionization-frontier",
        "inputs": inputs,
        "partial_support": partial_support,
        "requirements": requirements,
        "blockers": blockers,
        "cpt_fermionization_derived": all(requirements.values()),
        "keeps_C14_4_route_alive": False,
        "bottom_line": (
            "The repo has enough Pin/spinor machinery for boundary reflection and "
            "projection, but not enough to turn C,P,T into three occupiable "
            "fermionic boundary modes. The C(14,4)=1001 route remains alive only "
            "as a target: derive a CAR/Clifford boundary Hilbert law with C,P,T "
            "as physical modes, then select Lambda^4."
        ),
    }


def m31_symmetric_power_boundary_sector_candidate_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Audit the cleaner Sym^4(C^11) route from the M31 Janus Lie dimension."""

    required_n = int(math.ceil(1.0 + target_redshift))
    jan_lie_dimension = 11
    degree = 4
    sym_dimension = math.comb(jan_lie_dimension + degree - 1, degree)
    exterior_dimension = math.comb(jan_lie_dimension, degree)
    return {
        "status": "janus-m31-symmetric-power-boundary-sector-candidate",
        "source_anchor": "M31 Janus symplectic group",
        "published_inputs": {
            "Janus_Lie_group_dimension": jan_lie_dimension,
            "torsor_components": "ell(3), g(3), p(3), E(1), q(1)",
            "spacetime_translation_dimension": degree,
            "stress_energy_vector_dimension": degree,
        },
        "candidate_construction": {
            "formula": "dim Sym^4(C^11) = C(11+4-1,4) = C(14,4) = 1001",
            "sector_dimension": sym_dimension,
            "matches_required_N": sym_dimension == required_n,
            "uses_CPT_discrete_labels_as_modes": False,
            "compare_exterior_Lambda4_C11": exterior_dimension,
        },
        "why_stronger_than_exterior_11_plus_3": [
            "uses only the published continuous Janus Lie/torsor dimension 11",
            "degree 4 is anchored by the R4 translation/stress-energy sector",
            "does not require turning C,P,T discrete labels into one-particle modes",
        ],
        "why_not_closed": {
            "boundary_bosonic_Fock_or_symmetric_statistics_derived": False,
            "degree4_sector_selected_by_boundary_constraint": False,
            "Sym4_sector_maps_to_a_min": False,
            "Sym4_sector_maps_to_photon_ruler_dynamics": False,
        },
        "non_rustine_next_step": (
            "derive a boundary Hilbert law where the 11 M31 torsor/Lie modes are "
            "bosonic boundary modes and the R4 translation/stress-energy block "
            "selects homogeneous degree 4 states"
        ),
        "verdict": "best_current_structural_candidate_but_not_a_derivation",
    }


def m31_sym4_boundary_state_law_derivation_attempt_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Attempt to close Sym^4(C^11) as a Janus boundary state law."""

    candidate = m31_symmetric_power_boundary_sector_candidate_payload(target_redshift)
    required_n = candidate["candidate_construction"]["sector_dimension"]
    derivation_steps = [
        {
            "step": "M31 supplies an 11-dimensional Janus Lie/torsor vector space V",
            "status": "source_anchored",
        },
        {
            "step": "Bosonic quantization of V gives homogeneous polynomial sectors Sym^d(V)",
            "status": "standard_mathematical_construction",
        },
        {
            "step": "For d=4, dim Sym^4(C^11)=1001",
            "status": "proved_by_dimension_formula",
        },
        {
            "step": "Degree d=4 is physically selected by Janus R4 translation/stress-energy block",
            "status": "plausible_but_not_derived",
        },
        {
            "step": "The Sym^4 sector fixes early a_min=1/1001",
            "status": "model_law_required",
        },
        {
            "step": "That a_min enters photon/ruler dynamics",
            "status": "map_required",
        },
    ]
    closed_steps = [
        row["step"]
        for row in derivation_steps
        if row["status"] in {"source_anchored", "standard_mathematical_construction", "proved_by_dimension_formula"}
    ]
    open_steps = [row["step"] for row in derivation_steps if row["step"] not in closed_steps]
    return {
        "status": "janus-m31-sym4-boundary-state-law-derivation-attempt",
        "candidate": "Sym^4(C^11)",
        "required_N": required_n,
        "derivation_steps": derivation_steps,
        "closed_steps": closed_steps,
        "open_steps": open_steps,
        "if_last_two_steps_are_accepted": {
            "N_selected": required_n,
            "a_min": 1.0 / required_n,
            "geometric_z_max": required_n - 1.0,
            "pre_drag_reach": True,
        },
        "no_fit_closed_now": False,
        "new_principle_needed": (
            "Janus boundary state law: physical boundary Hilbert sector is the "
            "homogeneous degree-4 bosonic sector Sym^4(jan_C^*) and its dimension "
            "sets the early-throat inverse scale."
        ),
        "bottom_line": (
            "This is the strongest current route. It closes the number 1001 from "
            "M31 plus standard symmetric-power counting, without CPT mode mixing. "
            "It still needs one genuine Janus principle: why the boundary state "
            "law selects Sym^4 and why dim(Sym^4) sets a_min."
        ),
    }


def boundary_dimension_to_amin_map_audit_payload(
    target_redshift: float = 1000.0,
    N: int = 1001,
) -> dict:
    """Audit possible maps from a boundary Hilbert dimension to early a_min."""

    required_a_min = 1.0 / (1.0 + target_redshift)
    maps = [
        {
            "name": "linear_resolution_length",
            "formula": "a_min = 1/N",
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "matches_predrag": True,
            "derived": False,
            "physical_reading": "N counts linear resolution cells along the redshift/throat scale",
        },
        {
            "name": "area_resolution",
            "formula": "a_min = 1/sqrt(N)",
            "a_min": 1.0 / math.sqrt(N),
            "z_max": math.sqrt(N) - 1.0,
            "matches_predrag": math.sqrt(N) - 1.0 >= target_redshift,
            "derived": False,
            "physical_reading": "N counts area cells on a two-surface",
        },
        {
            "name": "volume_resolution",
            "formula": "a_min = 1/N^(1/3)",
            "a_min": 1.0 / (N ** (1.0 / 3.0)),
            "z_max": N ** (1.0 / 3.0) - 1.0,
            "matches_predrag": N ** (1.0 / 3.0) - 1.0 >= target_redshift,
            "derived": False,
            "physical_reading": "N counts volume cells on a three-dimensional throat/collar",
        },
        {
            "name": "entropy_dimension",
            "formula": "a_min = exp(-log(N)/3)",
            "a_min": math.exp(-math.log(N) / 3.0),
            "z_max": math.exp(math.log(N) / 3.0) - 1.0,
            "matches_predrag": math.exp(math.log(N) / 3.0) - 1.0 >= target_redshift,
            "derived": False,
            "physical_reading": "Hilbert dimension is entropy of a three-dimensional state volume",
        },
    ]
    successful = [row["name"] for row in maps if row["matches_predrag"]]
    return {
        "status": "janus-boundary-dimension-to-amin-map-audit",
        "N": N,
        "required_a_min": required_a_min,
        "maps": maps,
        "successful_maps": successful,
        "unique_success_is_linear_resolution": successful == ["linear_resolution_length"],
        "current_map_derived": False,
        "bottom_line": (
            "Even if Sym^4(C^11) supplies N=1001, BAO reach follows only if "
            "N is a linear throat/redshift resolution count. Area, volume and "
            "entropy readings give z_max far below 1000. Therefore the remaining "
            "hard step is specifically a linear-resolution boundary law, not just "
            "a Hilbert dimension."
        ),
    }


def sym4_linear_resolution_law_candidate_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Candidate law connecting Sym^4(C^11) to a linear throat/redshift scale."""

    sym4 = m31_sym4_boundary_state_law_derivation_attempt_payload(target_redshift)
    N = sym4["required_N"]
    return {
        "status": "janus-sym4-linear-resolution-law-candidate",
        "inputs": {
            "N_from_Sym4_C11": N,
            "early_branch_has_one_dimensional_normal_or_redshift_channel": True,
            "linear_map_required_for_predrag": True,
        },
        "candidate_law": (
            "The Sym^4 boundary sector counts normal/redshift resolution states "
            "along the one-dimensional throat evolution channel, so a_min=1/N."
        ),
        "why_physically_plausible": [
            "redshift reach is controlled by the one-dimensional branch coordinate, not by Sigma area",
            "the early cosh branch already reduces pre-drag reach to a one-dimensional a_min problem",
            "M31 degree 4 supplies the state-sector count; the throat channel supplies linear use of that count",
        ],
        "why_not_derived": {
            "normal_channel_spectral_operator_defined": False,
            "Sym4_states_identified_with_normal_resolution_cells": False,
            "a_min_equals_inverse_state_count_proved": False,
            "matching_to_photon_ruler_dynamics_proved": False,
        },
        "if_accepted": {
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "bottom_line": (
            "This is the cleanest physical interpretation of the required linear "
            "map: Sym^4(C^11) counts states along the normal/redshift throat "
            "channel. It is coherent, but it still requires a derived normal-channel "
            "spectral operator or equivalent boundary state law."
        ),
    }


def sym4_normal_channel_spectral_operator_candidate_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Audit whether a normal-channel spectral operator can justify a_min=1/N."""

    linear = sym4_linear_resolution_law_candidate_payload(target_redshift)
    N = linear["inputs"]["N_from_Sym4_C11"]
    return {
        "status": "janus-sym4-normal-channel-spectral-operator-candidate",
        "inputs": {
            "N_from_Sym4_C11": N,
            "candidate_operator_family": "self_adjoint_1d_normal_channel_sturm_liouville",
            "normal_coordinate": "redshift/throat coordinate s in [0,1]",
            "boundary_conditions": "Z2/PT endpoint parity plus regular throat endpoint",
        },
        "operator_attempt": {
            "linear_mode_indexing_available": True,
            "one_dimensional_resolution_interpretation_available": True,
            "self_adjoint_boundary_problem_available": True,
            "spectrum_infinite_without_cutoff": True,
            "finite_N_selected_by_operator_alone": False,
            "finite_N_selected_by_Sym4_sector": True,
        },
        "what_this_closes": [
            "a mathematically standard 1D normal-channel spectrum can support linear mode counting",
            "if a finite Sym4 boundary Hilbert sector is imposed, its dimension gives N=1001",
            "then a_min=1/N reaches z=1000",
        ],
        "what_remains_open": {
            "derive_the_specific_normal_operator_from_Janus_PT_action": False,
            "derive_boundary_conditions_from_resolved_tunnel_geometry": False,
            "derive_finite_bandlimit_from_Sym4_state_law": False,
            "prove_a_min_equals_inverse_bandlimit": False,
            "prove_photon_baryon_ruler_uses_same_normal_channel": False,
        },
        "if_all_open_steps_are_derived": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The spectral-operator route makes the linear map physically sharp, "
            "but it does not close it alone: an ordinary 1D operator has an "
            "infinite spectrum. The non-rustine theorem still needed is a Janus/PT "
            "boundary state law that turns Sym^4(C^11) into the finite bandlimit "
            "of the normal/redshift channel."
        ),
    }


def sym4_finite_transfer_operator_candidate_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Stronger route: make the normal/redshift evolution operator finite from Sym4."""

    spectral = sym4_normal_channel_spectral_operator_candidate_payload(target_redshift)
    N = spectral["inputs"]["N_from_Sym4_C11"]
    return {
        "status": "janus-sym4-finite-transfer-operator-candidate",
        "candidate": (
            "normal/redshift evolution is a finite transfer operator acting on "
            "the boundary Hilbert sector Sym^4(C^11)"
        ),
        "inputs": {
            "Hilbert_sector": "Sym^4(C^11)",
            "Hilbert_dimension": N,
            "continuous_Janus_modes": 11,
            "homogeneous_degree": 4,
        },
        "why_stronger_than_continuum_spectral_cutoff": [
            "finite N is intrinsic to the Hilbert sector, not imposed on an infinite spectrum",
            "normal/redshift evolution is a transfer problem on boundary states",
            "the one-dimensional throat coordinate can be emergent ordering of finite states",
        ],
        "operator_requirements": {
            "finite_transfer_matrix_on_Sym4_defined": False,
            "self_adjoint_or_unitary_evolution_rule_defined": False,
            "Z2_PT_symmetry_commutes_with_transfer": False,
            "ordered_normal_resolution_spectrum_derived": False,
            "ground_to_top_state_count_equals_inverse_a_min": False,
            "photon_baryon_drag_uses_same_transfer_clock": False,
        },
        "what_would_close_if_derived": {
            "N_selected_without_cutoff": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "next_hard_object": (
            "derive a Janus/PT boundary Hamiltonian or transfer generator on "
            "Sym^4(C^11), with Z2/PT covariance and a monotone normal/redshift "
            "spectrum whose endpoint count is 1001"
        ),
        "bottom_line": (
            "This is stronger than a continuum Sturm-Liouville cutoff because the "
            "finite dimension is not added by hand. It still lacks the physical "
            "transfer generator. If that generator is derived, the Sym4 route can "
            "become a genuine no-fit early-ruler sector."
        ),
    }


def sym4_transfer_generator_candidate_matrix_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Test natural transfer-generator candidates for the Sym4 boundary sector."""

    finite = sym4_finite_transfer_operator_candidate_payload(target_redshift)
    N = finite["inputs"]["Hilbert_dimension"]
    candidates = [
        {
            "name": "M31_quadratic_Casimir",
            "anchored": True,
            "finite_on_Sym4": True,
            "orders_normal_redshift_states": False,
            "failure": "Casimir classifies representation blocks; it does not create a 1001-step normal ordering inside Sym4.",
        },
        {
            "name": "R4_translation_or_stress_energy_number",
            "anchored": True,
            "finite_on_Sym4": True,
            "orders_normal_redshift_states": False,
            "failure": "degree-4 occupation is constant on Sym4, so the number operator cannot resolve 1001 levels.",
        },
        {
            "name": "PT_modular_or_orientation_flow",
            "anchored": True,
            "finite_on_Sym4": False,
            "orders_normal_redshift_states": False,
            "failure": "PT fixes parity/orientation constraints, but no modular Hamiltonian or density matrix is derived.",
        },
        {
            "name": "basis_path_graph_transfer",
            "anchored": False,
            "finite_on_Sym4": True,
            "orders_normal_redshift_states": True,
            "failure": "a path ordering of basis states would be arbitrary unless derived from Janus/PT geometry.",
        },
        {
            "name": "boundary_Hamiltonian_from_action",
            "anchored": False,
            "finite_on_Sym4": True,
            "orders_normal_redshift_states": False,
            "failure": "this is the needed object, but it is not yet present in the paper-native or derived action layer.",
        },
    ]
    non_rustine_closers = [
        row["name"]
        for row in candidates
        if row["anchored"] and row["finite_on_Sym4"] and row["orders_normal_redshift_states"]
    ]
    return {
        "status": "janus-sym4-transfer-generator-candidate-matrix",
        "inputs": {
            "Hilbert_sector": "Sym^4(C^11)",
            "Hilbert_dimension": N,
            "target": "derive a non-arbitrary 1001-step normal/redshift ordering",
        },
        "candidates": candidates,
        "non_rustine_closers": non_rustine_closers,
        "any_non_rustine_closer": bool(non_rustine_closers),
        "next_required_theorem": (
            "derive a boundary Hamiltonian/modular generator from the Janus/PT "
            "action or symplectic boundary form, then prove its ordered spectrum "
            "on Sym^4(C^11) has 1001 endpoint resolution states"
        ),
        "no_fit_closed_now": False,
        "bottom_line": (
            "The natural anchored generators do not order the 1001 Sym4 states. "
            "The only ordering candidate is a path/transfer graph, but that is a "
            "rustine unless the graph is derived from Janus/PT boundary dynamics."
        ),
    }


def sym4_diagonal_hamiltonian_ordering_audit_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Audit diagonal Hamiltonians on Sym4 against M31 block/isotropy constraints."""

    matrix = sym4_transfer_generator_candidate_matrix_payload(target_redshift)
    N = matrix["inputs"]["Hilbert_dimension"]
    degree = 4
    physical_blocks = {
        "ell": 3,
        "g": 3,
        "p": 3,
        "E": 1,
        "q": 1,
    }
    block_count_profiles = math.comb(degree + len(physical_blocks) - 1, degree)
    return {
        "status": "janus-sym4-diagonal-hamiltonian-ordering-audit",
        "inputs": {
            "Hilbert_sector": "Sym^4(C^11)",
            "basis_dimension": N,
            "degree": degree,
            "M31_blocks": physical_blocks,
        },
        "diagonal_hamiltonian_cases": [
            {
                "case": "isotropic_block_weights",
                "description": "one weight per M31 physical block ell,g,p,E,q",
                "max_distinct_profiles": block_count_profiles,
                "can_order_all_1001_states": block_count_profiles >= N,
                "verdict": "too_degenerate",
            },
            {
                "case": "componentwise_weights_inside_triplets",
                "description": "separate weights for components inside ell,g,p triplets",
                "max_distinct_profiles": N,
                "can_order_all_1001_states": True,
                "verdict": "requires_anisotropic_or_unpublished_component_selector",
            },
            {
                "case": "generic_random_weights",
                "description": "generic weights split all monomials",
                "max_distinct_profiles": N,
                "can_order_all_1001_states": True,
                "verdict": "mathematically_possible_but_rustine_without_Janus_origin",
            },
        ],
        "no_fit_conclusion": {
            "isotropic_M31_diagonal_generator_orders_all_states": False,
            "full_ordering_requires_extra_selector": True,
            "extra_selector_options": [
                "preferred spatial direction on boundary",
                "non-diagonal transfer generator from action",
                "modular Hamiltonian/density matrix",
                "boundary graph derived from PT/tunnel geometry",
            ],
        },
        "if_extra_selector_is_derived": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "A diagonal Hamiltonian respecting only the published M31 block "
            "structure and isotropy has at most C(8,4)=70 occupation profiles, "
            "not 1001. Splitting all 1001 states requires an additional selector "
            "inside the triplets or a non-diagonal boundary transfer generator."
        ),
    }


def m31_to_sym4_boundary_representation_gap_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Track what is missing between M31 torsor action and a Sym4 transfer generator."""

    diagonal = sym4_diagonal_hamiltonian_ordering_audit_payload(target_redshift)
    N = diagonal["inputs"]["basis_dimension"]
    chain = [
        {
            "step": "M31 coadjoint/torsor action available",
            "available": True,
            "note": "source gives transformations of torsor components and energy/momentum/charge interpretation",
        },
        {
            "step": "identify boundary mode space V with C^11",
            "available": True,
            "note": "structural candidate: 11 continuous Janus torsor modes",
        },
        {
            "step": "derive rho: janus_lie -> End(V)",
            "available": False,
            "note": "torsor action is not yet a boundary Hilbert representation on V",
        },
        {
            "step": "lift rho to Sym^4(V)",
            "available": False,
            "note": "standard once rho exists",
        },
        {
            "step": "select normal/redshift transfer generator H",
            "available": False,
            "note": "no published or derived normal Hamiltonian in the active branch",
        },
        {
            "step": "prove ordered 1001-state spectrum maps to a_min",
            "available": False,
            "note": "requires H and a clock/ruler map",
        },
    ]
    return {
        "status": "janus-m31-to-sym4-boundary-representation-gap",
        "inputs": {
            "source_anchor": "M31 Janus symplectic group action on torsors",
            "target_Hilbert_sector": "Sym^4(C^11)",
            "target_dimension": N,
        },
        "derivation_chain": chain,
        "closed_steps": [row["step"] for row in chain if row["available"]],
        "open_steps": [row["step"] for row in chain if not row["available"]],
        "minimal_missing_object": "rho: janus_lie -> End(C^11) plus a normal/redshift Hamiltonian H",
        "why_this_is_not_a_numeric_fit": (
            "The missing object is structural: it would define how the published "
            "Janus symmetry transports boundary states. No observational parameter "
            "is being adjusted here."
        ),
        "if_closed": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "M31 supplies the symmetry/torsor anchor, but not yet the boundary "
            "Hilbert representation or normal Hamiltonian needed to turn Sym4 "
            "into an ordered early-universe ruler."
        ),
    }


def m31_coadjoint_rho_transfer_attempt_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Use the M31 coadjoint/torsor action as the rho candidate and audit H."""

    gap = m31_to_sym4_boundary_representation_gap_payload(target_redshift)
    N = gap["inputs"]["target_dimension"]
    generators = [
        {
            "name": "Lorentz_rotation_block",
            "rho_available": True,
            "lift_to_Sym4_available": True,
            "normal_redshift_H": False,
            "reason": "compact rotations preserve spatial isotropy sectors; they do not define cosmological normal time.",
        },
        {
            "name": "Lorentz_boost_block",
            "rho_available": True,
            "lift_to_Sym4_available": True,
            "normal_redshift_H": False,
            "reason": "boosts are observer-frame changes, not a throat endpoint evolution law.",
        },
        {
            "name": "spacetime_translation_coadjoint_shear",
            "rho_available": True,
            "lift_to_Sym4_available": True,
            "normal_redshift_H": False,
            "reason": "translations shear angular/boost moments by P but do not yield a self-adjoint 1001-level normal clock.",
        },
        {
            "name": "fifth_charge_translation_or_reflection",
            "rho_available": True,
            "lift_to_Sym4_available": True,
            "normal_redshift_H": False,
            "reason": "charge is invariant or sign-flipped; this gives sectors, not ordered redshift levels.",
        },
    ]
    return {
        "status": "janus-m31-coadjoint-rho-transfer-attempt",
        "inputs": {
            "rho_candidate": "M31 coadjoint action on torsor components (l,g,p,E,q)",
            "target_Hilbert_sector": "Sym^4(C^11)",
            "target_dimension": N,
        },
        "what_progresses": {
            "rho_candidate_from_M31_available": True,
            "standard_lift_to_Sym4_available": True,
            "boundary_representation_gap_partially_closed": True,
        },
        "generator_audit": generators,
        "normal_redshift_generator_found": any(row["normal_redshift_H"] for row in generators),
        "remaining_gap": (
            "M31 coadjoint rho can be used as a representation candidate, but "
            "none of its natural published generators is the normal/redshift "
            "transfer Hamiltonian needed by the early-ruler branch."
        ),
        "non_rustine_next_step": (
            "derive a boundary Hamiltonian from the resolved PT/Sigma action or "
            "a modular state, then check whether it is built from the M31 "
            "coadjoint generators"
        ),
        "if_normal_H_is_derived": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "This is progress: rho is no longer purely missing if we accept the "
            "coadjoint torsor action as boundary representation. The remaining "
            "hard blocker is now sharper: identify a physical normal/redshift "
            "Hamiltonian inside, or derived from, that representation."
        ),
    }


def normal_redshift_hamiltonian_route_matrix_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Rank non-rustine routes for the missing normal/redshift Hamiltonian."""

    coadjoint = m31_coadjoint_rho_transfer_attempt_payload(target_redshift)
    N = coadjoint["inputs"]["target_dimension"]
    routes = [
        {
            "name": "PT_Sigma_boundary_action_H",
            "non_rustine": True,
            "could_close": True,
            "requires": [
                "boundary symplectic potential theta_Sigma",
                "normal/throat evolution vector field X_normal",
                "Hamiltonian relation delta H = i_X Omega_boundary",
                "representation on Sym4(C11)",
            ],
            "status": "best_next_route",
        },
        {
            "name": "boundary_modular_H",
            "non_rustine": True,
            "could_close": True,
            "requires": [
                "boundary density matrix or state law",
                "modular flow compatible with PT",
                "projection to Sym4(C11)",
            ],
            "status": "credible_but_needs_state_law",
        },
        {
            "name": "geometric_throat_length_operator",
            "non_rustine": True,
            "could_close": False,
            "requires": [
                "active normal coordinate",
                "absolute length or endpoint law",
                "map from length spectrum to Sym4 states",
            ],
            "status": "insufficient_alone_because_scale_returns",
        },
        {
            "name": "KKS_moment_map_selected_generator",
            "non_rustine": True,
            "could_close": False,
            "requires": [
                "selected normal generator X in Janus Lie algebra",
                "nonzero KKS period",
                "compact boundary orbit",
            ],
            "status": "blocked_because_natural_M31_generators_are_not_H_normal",
        },
        {
            "name": "empirical_or_lexicographic_ordering",
            "non_rustine": False,
            "could_close": False,
            "requires": ["manual order of basis states"],
            "status": "rejected_rustine",
        },
    ]
    viable = [row["name"] for row in routes if row["non_rustine"] and row["could_close"]]
    return {
        "status": "janus-normal-redshift-hamiltonian-route-matrix",
        "inputs": {
            "rho_candidate": coadjoint["inputs"]["rho_candidate"],
            "Hilbert_sector": "Sym^4(C^11)",
            "Hilbert_dimension": N,
        },
        "routes": routes,
        "viable_non_rustine_routes": viable,
        "recommended_next_route": "PT_Sigma_boundary_action_H",
        "why": (
            "Only a boundary-action Hamiltonian can derive both the generator "
            "and its symplectic normalization without ordering states by hand. "
            "The modular route is second-best but needs an independent state law."
        ),
        "if_recommended_route_closes": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The next real calculation is not more numerology around 1001. It is "
            "a PT/Sigma boundary Hamiltonian derivation: construct theta_Sigma "
            "and Omega_boundary, identify X_normal, then test its lifted action "
            "on Sym4(C11)."
        ),
    }


def noether_boundary_charge_to_sym4_transfer_bridge_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Bridge existing Z2/Sigma Noether boundary charge work to the Sym4 route."""

    route = normal_redshift_hamiltonian_route_matrix_payload(target_redshift)
    N = route["inputs"]["Hilbert_dimension"]
    return {
        "status": "janus-noether-boundary-charge-to-sym4-transfer-bridge",
        "existing_z2_sigma_boundary_charge": {
            "covariant_phase_space_formula_declared": True,
            "formula": "delta H_xi = integral_Sigma (delta Q_xi - i_xi theta)",
            "brown_york_symbolic_reduction": "E_BY = kappa^-1 integral_Sigma N sqrt(q) (k_ref-k_phys)",
            "symbolic_charge": "12*pi^2*R_Sigma^2/kappa_Z2Sigma",
            "symbolic_boundary_hamiltonian_ready": True,
            "numeric_boundary_hamiltonian_ready": False,
            "blocked_by": [
                "boundary_charge_value_available",
                "absolute_surface_measure_available",
                "physical_lapse_normalization_available",
            ],
        },
        "sym4_transfer_bridge_requirements": {
            "use_boundary_H_as_normal_generator": False,
            "map_boundary_H_to_End_Sym4C11": False,
            "prove_Z2_PT_covariance": False,
            "prove_ordered_1001_spectrum": False,
            "prove_same_clock_for_photon_drag": False,
        },
        "what_this_reuses": [
            "Noether/covariant phase-space Hamiltonian formula",
            "Brown-York symbolic boundary energy reduction",
            "plus/minus boundary leg inventory",
        ],
        "what_it_does_not_solve": [
            "absolute throat scale or physical lapse",
            "nonzero renormalized boundary charge",
            "operator action on Sym4(C11)",
            "ordered redshift spectrum",
        ],
        "if_bridge_closes": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The old Z2/Sigma Hamiltonian boundary work is the right source for "
            "theta_Sigma/Omega_boundary, but it is still symbolic and scale-free. "
            "To close the Sym4 early-ruler route, it must produce a physical "
            "normal Hamiltonian and a representation on Sym4(C11)."
        ),
    }


def boundary_hamiltonian_scalar_vs_operator_audit_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Audit whether the Noether/Brown-York boundary Hamiltonian can order Sym4."""

    bridge = noether_boundary_charge_to_sym4_transfer_bridge_payload(target_redshift)
    N = bridge["if_bridge_closes"]["N_selected"]
    cases = [
        {
            "case": "scalar_boundary_energy",
            "form": "H_boundary * Identity_on_Sym4",
            "source": "Brown-York/Noether scalar energy",
            "orders_1001_states": False,
            "reason": "a scalar Hamiltonian has one eigenvalue on the Hilbert sector",
        },
        {
            "case": "m31_vector_valued_boundary_charge",
            "form": "sum_A H_A rho(T_A) on Sym4(C11)",
            "source": "would require boundary charges for M31 generators",
            "orders_1001_states": False,
            "reason": "not yet derived; isotropic published blocks remain too degenerate",
        },
        {
            "case": "non_diagonal_boundary_transfer",
            "form": "H_normal derived from theta_Sigma/Omega_boundary",
            "source": "PT/Sigma action or modular state",
            "orders_1001_states": False,
            "reason": "the required object is identified but unavailable",
        },
    ]
    return {
        "status": "janus-boundary-hamiltonian-scalar-vs-operator-audit",
        "inputs": {
            "Hilbert_sector": "Sym^4(C^11)",
            "Hilbert_dimension": N,
            "existing_boundary_H": bridge["existing_z2_sigma_boundary_charge"]["formula"],
        },
        "cases": cases,
        "scalar_boundary_H_orders_states": False,
        "operator_valued_boundary_H_available": False,
        "minimal_operator_requirement": (
            "derive M31-valued or non-diagonal H_normal from PT/Sigma boundary "
            "phase space, not just scalar Brown-York energy"
        ),
        "if_operator_requirement_closes": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The existing Noether/Brown-York boundary Hamiltonian is the correct "
            "energy charge, but as a scalar it acts as identity on Sym4(C11). "
            "It cannot generate the 1001-level redshift ordering. The branch "
            "needs an operator-valued boundary Hamiltonian or non-diagonal "
            "transfer generator derived from PT/Sigma data."
        ),
    }


def plus_minus_boundary_leg_operator_audit_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Audit whether plus/minus Sigma legs can provide the missing Sym4 operator."""

    scalar = boundary_hamiltonian_scalar_vs_operator_audit_payload(target_redshift)
    N = scalar["inputs"]["Hilbert_dimension"]
    return {
        "status": "janus-plus-minus-boundary-leg-operator-audit",
        "inputs": {
            "Hilbert_sector": "Sym^4(C^11)",
            "Hilbert_dimension": N,
            "boundary_legs": ["plus", "minus"],
        },
        "operator_candidates": [
            {
                "name": "leg_difference_operator",
                "form": "diag(H_plus, H_minus)",
                "max_levels": 2,
                "can_order_1001_states": False,
                "role": "sector splitting only",
            },
            {
                "name": "leg_mixing_PT_operator",
                "form": "[[H_plus, J_PT], [J_PT, H_minus]]",
                "max_levels": 2,
                "can_order_1001_states": False,
                "role": "PT doublet mixing only unless tensored with Sym4 generator",
            },
            {
                "name": "leg_operator_tensor_sym4_identity",
                "form": "H_leg tensor I_Sym4",
                "max_levels": 2,
                "can_order_1001_states": False,
                "role": "does not split Sym4 internal states",
            },
            {
                "name": "leg_operator_coupled_to_M31_transfer",
                "form": "H_leg tensor H_M31_normal",
                "max_levels": N,
                "can_order_1001_states": False,
                "role": "would work only if H_M31_normal is independently derived",
            },
        ],
        "no_fit_conclusion": {
            "plus_minus_legs_supply_nontrivial_operator": True,
            "plus_minus_legs_alone_supply_1001_ordering": False,
            "legs_can_help_as_PT_doublet_factor": True,
            "still_need_sym4_internal_transfer": True,
        },
        "if_internal_transfer_is_derived": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The plus/minus boundary legs can give a real PT doublet operator, "
            "but by themselves they have at most two levels. They cannot replace "
            "the missing Sym4 internal normal-transfer Hamiltonian."
        ),
    }


def sym4_internal_transfer_frontier_verdict_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Summarize the exhausted routes and the remaining hard object."""

    legs = plus_minus_boundary_leg_operator_audit_payload(target_redshift)
    N = legs["inputs"]["Hilbert_dimension"]
    exhausted = [
        "scalar Brown-York/Noether boundary energy: identity on Sym4",
        "M31 isotropic block diagonal Hamiltonian: at most 70 profiles",
        "natural M31 coadjoint generators: no normal/redshift Hamiltonian",
        "plus/minus PT leg operator: at most 2 levels",
        "manual basis ordering: rejected as rustine",
    ]
    remaining = [
        "derive non-diagonal H_normal from PT/Sigma boundary action",
        "or derive modular Hamiltonian from a boundary state law",
        "prove H_normal acts on Sym4(C11)",
        "prove ordered endpoint count gives a_min=1/1001",
        "prove photon-baryon drag uses the same normal clock",
    ]
    return {
        "status": "janus-sym4-internal-transfer-frontier-verdict",
        "target": {
            "Hilbert_sector": "Sym^4(C^11)",
            "Hilbert_dimension": N,
            "a_min_if_closed": 1.0 / N,
            "z_max_if_closed": N - 1.0,
        },
        "exhausted_routes": exhausted,
        "remaining_hard_objects": remaining,
        "current_best_non_rustine_route": "non_diagonal_PT_Sigma_boundary_action_H_normal",
        "frontier_interpretation": (
            "The problem is no longer finding the integer 1001. It is deriving "
            "a physical internal transfer Hamiltonian whose spectrum uses those "
            "1001 states as the early redshift/ruler resolution."
        ),
        "no_fit_closed_now": False,
        "stop_condition_for_this_subbranch": (
            "continue only by deriving H_normal from the action/modular state; "
            "do not add more combinatorial selectors"
        ),
        "bottom_line": (
            "All simple operator sources have been exhausted. The next advance "
            "must be a real action-level or modular derivation of a non-diagonal "
            "Sym4 internal transfer generator."
        ),
    }


def sym4_schur_irreducibility_obstruction_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Use irreducibility to constrain possible Sym4 Hamiltonians."""

    verdict = sym4_internal_transfer_frontier_verdict_payload(target_redshift)
    N = verdict["target"]["Hilbert_dimension"]
    return {
        "status": "janus-sym4-schur-irreducibility-obstruction",
        "representation": {
            "sector": "Sym^4(C^11)",
            "dimension": N,
            "natural_group": "GL(11,C) / SU(11)-type linear action",
            "irreducible_under_natural_action": True,
        },
        "schur_consequence": {
            "fully_symmetric_operator_is_scalar": True,
            "fully_symmetric_H_orders_1001_states": False,
            "nontrivial_H_requires_symmetry_breaking_or_external_generator": True,
        },
        "allowed_nontrivial_H_sources": [
            "PT/Sigma boundary action selects a normal generator",
            "boundary modular state selects a density matrix",
            "physical subgroup reduction selects an internal direction",
            "operator-valued boundary charge breaks full Sym4 symmetry in a derived way",
        ],
        "forbidden_reading": (
            "do not demand full Sym4/M31 invariance and a nontrivial 1001-level "
            "spectrum simultaneously"
        ),
        "if_allowed_source_is_derived": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "This is a genuine mathematical restriction: if the boundary Hilbert "
            "sector is Sym^4(C^11), then a fully invariant Hamiltonian is scalar. "
            "The needed H_normal must be a derived symmetry-breaking or modular "
            "operator, not a fully symmetric charge."
        ),
    }


def hnormal_symmetry_breaking_candidate_matrix_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Rank symmetry-breaking sources that could legally evade Schur."""

    schur = sym4_schur_irreducibility_obstruction_payload(target_redshift)
    N = schur["representation"]["dimension"]
    candidates = [
        {
            "name": "PT_normal_generator",
            "janus_anchored": True,
            "breaks_full_Sym4_symmetry": True,
            "defines_operator_now": False,
            "risk": "PT supplies orientation/normal direction but not the internal Sym4 matrix.",
            "rank": 1,
        },
        {
            "name": "boundary_modular_state",
            "janus_anchored": False,
            "breaks_full_Sym4_symmetry": True,
            "defines_operator_now": False,
            "risk": "powerful but needs a state law or density matrix not yet derived.",
            "rank": 2,
        },
        {
            "name": "cosmological_time_generator",
            "janus_anchored": True,
            "breaks_full_Sym4_symmetry": True,
            "defines_operator_now": False,
            "risk": "time flow is physical, but current boundary Hamiltonian is scalar.",
            "rank": 3,
        },
        {
            "name": "componentwise_triplet_direction",
            "janus_anchored": False,
            "breaks_full_Sym4_symmetry": True,
            "defines_operator_now": True,
            "risk": "orders states only by choosing an unpublished anisotropic direction.",
            "rank": 4,
        },
    ]
    admissible_now = [
        row["name"]
        for row in candidates
        if row["janus_anchored"] and row["defines_operator_now"]
    ]
    return {
        "status": "janus-hnormal-symmetry-breaking-candidate-matrix",
        "inputs": {
            "Hilbert_sector": "Sym^4(C^11)",
            "Hilbert_dimension": N,
            "Schur_obstruction_active": True,
        },
        "candidates": candidates,
        "admissible_closers_now": admissible_now,
        "recommended_attack": "PT_normal_generator_to_internal_Sym4_matrix",
        "reason": (
            "PT/Sigma is already part of the geometry and supplies the right kind "
            "of normal orientation. The missing step is deriving its internal "
            "matrix on the M31/Sym4 boundary sector."
        ),
        "if_recommended_attack_closes": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "Schur forces a symmetry-breaking source. The least arbitrary source "
            "is the PT/Sigma normal generator, but it still lacks a derived "
            "internal Sym4 matrix."
        ),
    }


def pt_normal_to_sym4_internal_matrix_attempt_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Attempt to turn PT/Sigma normal orientation into an internal Sym4 matrix."""

    matrix = hnormal_symmetry_breaking_candidate_matrix_payload(target_redshift)
    N = matrix["inputs"]["Hilbert_dimension"]
    actions = [
        {
            "action": "global_PT_sign_on_all_modes",
            "matrix_on_C11": "+/- Identity",
            "non_scalar_on_Sym4": False,
            "orders_1001_states": False,
            "verdict": "too_scalar",
        },
        {
            "action": "plus_minus_leg_exchange",
            "matrix_on_C11": "acts on external PT doublet, not internal C11",
            "non_scalar_on_Sym4": False,
            "orders_1001_states": False,
            "verdict": "external_doublet_only",
        },
        {
            "action": "CPT_component_signs_on_M31_blocks",
            "matrix_on_C11": "block signs on ell,g,p,E,q",
            "non_scalar_on_Sym4": True,
            "orders_1001_states": False,
            "verdict": "finite block splitting, not 1001 ordering",
        },
        {
            "action": "normal_connection_endomorphism",
            "matrix_on_C11": "A_normal from pullback connection on boundary modes",
            "non_scalar_on_Sym4": False,
            "orders_1001_states": False,
            "verdict": "needed but not derived",
        },
    ]
    return {
        "status": "janus-pt-normal-to-sym4-internal-matrix-attempt",
        "inputs": {
            "Hilbert_sector": "Sym^4(C^11)",
            "Hilbert_dimension": N,
            "source": "PT/Sigma normal orientation",
        },
        "tested_actions": actions,
        "derived_non_scalar_internal_matrix_now": False,
        "best_remaining_object": "normal_connection_endomorphism_A_normal_on_C11",
        "why_A_normal_is_needed": (
            "Only a connection/endormorphism acting on the 11 boundary modes can "
            "produce a genuine internal Sym4 transfer. PT signs and leg exchange "
            "are too coarse."
        ),
        "A_normal_requirements": {
            "boundary_mode_bundle_over_Sigma_declared": False,
            "normal_connection_on_mode_bundle_derived": False,
            "PT_covariance_of_connection_proved": False,
            "A_normal_lift_to_Sym4_defined": False,
            "A_normal_spectrum_orders_1001_states": False,
        },
        "if_A_normal_closes": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "PT/Sigma gives the right geometric source of symmetry breaking, but "
            "ordinary PT signs or plus/minus exchange are too coarse. The real "
            "object needed is a normal connection endomorphism on the 11 M31 "
            "boundary modes."
        ),
    }


def normal_connection_to_sym4_anormal_bridge_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Bridge existing normal-connection machinery to the required A_normal on C11."""

    attempt = pt_normal_to_sym4_internal_matrix_attempt_payload(target_redshift)
    N = attempt["inputs"]["Hilbert_dimension"]
    return {
        "status": "janus-normal-connection-to-sym4-anormal-bridge",
        "existing_normal_connection_machinery": {
            "calculator": "src/janus_lab/z2_sigma_normal_connection.py",
            "input_manifest": "outputs/active_z2_sigma/normal_connection_frame_primitives.json",
            "output_manifest": "outputs/active_z2_sigma/normal_connection_omega_perp_inputs.json",
            "calculator_ready": True,
            "active_input_manifest_present": False,
            "normal_connection_ready_now": False,
        },
        "bridge_requirements": {
            "active_normal_frame_primitives_materialized": False,
            "omega_perp_active_not_diagnostic": False,
            "rho_perp_to_End_C11_derived": False,
            "A_normal_on_C11_defined": False,
            "A_normal_lift_to_Sym4_defined": False,
            "A_normal_orders_1001_states": False,
        },
        "why_existing_omega_is_not_enough": [
            "omega_perp is a normal-frame connection matrix, not automatically an operator on M31 boundary modes",
            "diagnostic local/global twist probes are not active source-derived manifests",
            "the map rho_perp: normal-frame algebra -> End(C11) is still missing",
        ],
        "if_bridge_closes": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The repo already has the right low-level normal-connection calculator. "
            "The remaining work is not numerical plumbing; it is deriving the "
            "representation rho_perp that turns active omega_perp into A_normal "
            "on the 11 M31 boundary modes."
        ),
    }


def anormal_sym4_spectral_condition_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Make the exact spectral condition for A_normal on Sym4 explicit."""

    bridge = normal_connection_to_sym4_anormal_bridge_payload(target_redshift)
    N = bridge["if_bridge_closes"]["N_selected"]
    degree = 4
    dim_c11 = 11
    arithmetic_weights = list(range(dim_c11))
    base5_weights = [5**i for i in range(dim_c11)]
    return {
        "status": "janus-anormal-sym4-spectral-condition",
        "spectral_rule": (
            "If A_normal has C11 eigenweights w_i, the Sym4 lift has eigenvalues "
            "w_i+w_j+w_k+w_l over all multisets of degree 4."
        ),
        "target": {
            "C11_modes": dim_c11,
            "Sym_degree": degree,
            "Sym4_dimension": N,
            "required_distinct_levels": N,
        },
        "cases": [
            {
                "name": "scalar_weights",
                "distinct_levels": 1,
                "orders_1001": False,
                "janus_anchored": True,
                "verdict": "too_scalar",
            },
            {
                "name": "M31_block_profile_weights",
                "distinct_levels": math.comb(degree + 5 - 1, degree),
                "orders_1001": False,
                "janus_anchored": True,
                "verdict": "published block structure too degenerate",
            },
            {
                "name": "arithmetic_component_weights_0_to_10",
                "distinct_levels": _distinct_degree_sums(arithmetic_weights, degree),
                "orders_1001": False,
                "janus_anchored": False,
                "verdict": "component split still highly resonant",
            },
            {
                "name": "base5_dissociated_weights",
                "distinct_levels": _distinct_degree_sums(base5_weights, degree),
                "orders_1001": True,
                "janus_anchored": False,
                "verdict": "mathematically sufficient but not Janus-derived",
            },
        ],
        "necessary_condition": (
            "A_normal must have 11 eigenweights whose degree-4 multiset sums are all distinct."
        ),
        "janus_gap": (
            "derive 4-dissociated eigenweights from PT/Sigma normal holonomy, "
            "normal connection, or boundary modular state"
        ),
        "if_condition_is_derived": {
            "N_selected": N,
            "a_min": 1.0 / N,
            "z_max": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The exact mathematical target is now explicit: Janus must derive an "
            "A_normal with 4-dissociated eigenweights on C11. Generic or base-5 "
            "weights would work mathematically, but they are rustines unless they "
            "come from PT/Sigma geometry or a boundary state law."
        ),
    }


def anormal_weight_origin_candidate_matrix_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Classify possible Janus origins for the 11 A_normal eigenweights."""

    spectral = anormal_sym4_spectral_condition_payload(target_redshift)
    return {
        "status": "janus-anormal-weight-origin-candidate-matrix",
        "required_output": spectral["necessary_condition"],
        "candidates": [
            {
                "name": "scalar_quasilocal_boundary_charge",
                "janus_anchored": True,
                "orders_1001": False,
                "failure": "Brown-York/Noether scalar charge acts as identity on Sym4.",
            },
            {
                "name": "published_M31_block_weights",
                "janus_anchored": True,
                "orders_1001": False,
                "failure": "published block structure gives 70 degree-4 levels, not 1001.",
            },
            {
                "name": "topological_cycle_number_only",
                "janus_anchored": True,
                "orders_1001": False,
                "failure": "Z2/PT cycle data gives finite signs or sectors, not 11 four-dissociated weights.",
            },
            {
                "name": "active_PT_Sigma_normal_connection",
                "janus_anchored": True,
                "orders_1001": "possible_if_four_dissociated",
                "missing": [
                    "normal_connection_frame_primitives.json",
                    "rho_perp: normal-frame algebra -> End(C11)",
                    "proof that eigenweights of rho_perp(omega_perp) are four-dissociated",
                ],
            },
            {
                "name": "boundary_modular_state",
                "janus_anchored": "possible",
                "orders_1001": "possible_if_modular_spectrum_four_dissociated",
                "missing": [
                    "Janus/PT boundary density matrix or state law",
                    "modular Hamiltonian restricted to C11",
                    "four-dissociation proof for modular eigenweights",
                ],
            },
            {
                "name": "generic_base5_weight_law",
                "janus_anchored": False,
                "orders_1001": True,
                "failure": "works mathematically but is a rustine unless derived from Janus geometry/state.",
            },
        ],
        "rejected_as_no_fit_closures": [
            "scalar_quasilocal_boundary_charge",
            "published_M31_block_weights",
            "topological_cycle_number_only",
            "generic_base5_weight_law",
        ],
        "credible_remaining_routes": [
            "active_PT_Sigma_normal_connection",
            "boundary_modular_state",
        ],
        "next_physical_inputs": [
            "derive rho_perp from PT/Sigma normal transport on the M31 C11 mode bundle",
            "or derive a Janus/PT boundary state law whose modular Hamiltonian acts on C11",
        ],
        "no_fit_closed_now": False,
        "bottom_line": (
            "The frontier is now narrow. A valid no-fit route must produce a "
            "Janus-anchored non-scalar A_normal with four-dissociated C11 "
            "eigenweights. Existing scalar, block, or topological-cycle data "
            "cannot do it; generic weights would be arbitrary."
        ),
    }


def m31_compact_charge_to_anormal_weight_audit_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Audit the published compact charge dimensions as a source for A_normal weights."""

    matrix = anormal_weight_origin_candidate_matrix_payload(target_redshift)
    return {
        "status": "janus-m31-compact-charge-to-anormal-weight-audit",
        "source_anchor": {
            "paper": "EPJC 2024 Janus model / M31 Souriau-Kaluza charge sector",
            "local_extract": "outputs/janus_reference/extract_215_233.txt",
            "equation_range": "43-72",
            "claim_used": (
                "closed extra dimensions can encode quantum charges and PT/C "
                "sign actions on Souriau torsor scalars"
            ),
        },
        "what_it_closes": {
            "compact_charge_dimensions_declared": True,
            "charge_sign_under_PT_C_declared": True,
            "charge_quantization_motivation_declared": True,
        },
        "what_it_does_not_close": {
            "normal_redshift_generator_A_normal": False,
            "rho_perp_from_charge_lattice_to_End_C11": False,
            "four_dissociated_C11_weights": False,
            "a_min_or_BAO_ruler_no_fit": False,
        },
        "why_not_enough": [
            "Souriau/Kaluza charges label internal conserved scalars; they are not yet the normal-transfer Hamiltonian.",
            "ordinary charge lattices/signs give arithmetic or finite sector labels, which are generally resonant on Sym4.",
            "a map from compact charge lattice to the 11 C11 boundary modes is not derived in the paper-native source set.",
        ],
        "non_rustine_extension_path": [
            "derive compact charge torus/lattice on the PT/Sigma boundary",
            "derive its representation on the C11 mode bundle",
            "prove the induced charge-weight vector is four-dissociated",
            "only then use Sym4(C11) as the 1001-level early-ruler sector",
        ],
        "credible_remaining_routes_inherited": matrix["credible_remaining_routes"],
        "no_fit_closed_now": False,
        "bottom_line": (
            "The published compact-charge/Souriau sector is relevant and should be "
            "kept. It supports a possible boundary-state route, but by itself it "
            "does not supply the nonresonant A_normal spectrum needed for the "
            "native early-ruler closure."
        ),
    }


def quantum_fock_no_carry_anormal_candidate_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Candidate boundary-state law: no-carry occupation Hamiltonian on Sym4(C11)."""

    dim_c11 = 11
    degree = 4
    base = degree + 1
    weights = [base**i for i in range(dim_c11)]
    levels = _distinct_degree_sums(weights, degree)
    target_levels = math.comb(dim_c11 + degree - 1, degree)
    return {
        "status": "janus-quantum-fock-no-carry-anormal-candidate",
        "candidate_operator": "A_no_carry = sum_i base^i N_i on Sym^4(C11)",
        "inputs": {
            "C11_modes": dim_c11,
            "Sym_degree": degree,
            "base": base,
            "base_origin": "minimal no-carry base for occupations n_i in {0,...,4}",
            "weights": weights,
        },
        "spectrum": {
            "target_levels": target_levels,
            "distinct_levels": levels,
            "orders_all_Sym4_states": levels == target_levels,
            "z_max_if_used_as_N": target_levels - 1.0,
            "pre_drag_reach": target_levels - 1.0 >= target_redshift,
        },
        "why_interesting": [
            "uses the actual Sym4 Fock occupation structure instead of arbitrary labels",
            "base=5 is forced by degree 4 if the Hamiltonian must encode occupations without carry",
            "gives exactly 1001 ordered states without observational input",
        ],
        "not_yet_derived_from_janus": [
            "Janus/PT must provide an ordered 11-mode basis on C11",
            "Janus/PT must justify the no-carry modular Hamiltonian or q=5 boundary state law",
            "rho_perp must map normal/boundary transport to this occupation-number operator",
        ],
        "non_rustine_closure_condition": (
            "derive A_no_carry from PT/Sigma normal transport or from a boundary modular state, "
            "not by choosing weights after seeing the BAO target"
        ),
        "no_fit_closed_now": False,
        "bottom_line": (
            "This is the sharpest constructive candidate found so far. It exactly "
            "solves the 1001-level ordering problem, but it becomes Janus physics "
            "only if the ordered C11 mode chain and no-carry modular Hamiltonian "
            "are derived from PT/Sigma or the complex-reality boundary state."
        ),
    }


def souriau_torsor_c11_no_carry_bridge_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Try to anchor C11 in the published Souriau torsor components."""

    no_carry = quantum_fock_no_carry_anormal_candidate_payload(target_redshift)
    components = [
        {"name": "l", "meaning": "angular momentum", "dimension": 3},
        {"name": "g", "meaning": "boost/static moment", "dimension": 3},
        {"name": "p", "meaning": "linear momentum", "dimension": 3},
        {"name": "E", "meaning": "energy", "dimension": 1},
        {"name": "q", "meaning": "compact charge scalar", "dimension": 1},
    ]
    total_dim = sum(row["dimension"] for row in components)
    return {
        "status": "janus-souriau-torsor-c11-no-carry-bridge",
        "source_anchor": "published torsor mu={l,g,p,E,q}",
        "components": components,
        "C11_basis_identified": total_dim == 11,
        "canonical_block_filtration_available": True,
        "canonical_component_order_derived": False,
        "no_carry_operator_available_conditionally": no_carry["spectrum"]["orders_all_Sym4_states"],
        "what_progresses": {
            "C11_is_not_mysterious": True,
            "C11_can_be_read_as_Souriau_torsor_component_space": total_dim == 11,
            "Sym4_no_carry_operator_has_target_spectrum": no_carry["spectrum"]["orders_all_Sym4_states"],
        },
        "what_remains_unproved": {
            "ordered_component_chain_from_Janus_group_action": True,
            "why_torsor_components_should_have_base5_energy_hierarchy": True,
            "rho_perp_maps_normal_connection_to_torsor_number_operators": True,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "This is the best bridge between the published Janus/Souriau content "
            "and the quantum no-carry candidate. It anchors the 11-dimensional "
            "space, but the ordered no-carry Hamiltonian is still a boundary-state "
            "law unless the Janus group action derives the component order and "
            "base-5 hierarchy."
        ),
    }


def souriau_coadjoint_filtration_order_audit_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Use the published coadjoint action to test whether it orders C11."""

    bridge = souriau_torsor_c11_no_carry_bridge_payload(target_redshift)
    blocks = [
        {"name": "q", "dimension": 1, "coadjoint_role": "central/sign scalar"},
        {"name": "P=(E,p)", "dimension": 4, "coadjoint_role": "transforms without M"},
        {"name": "M=(l,g)", "dimension": 6, "coadjoint_role": "mixes with P under translations"},
    ]
    block_profile_levels = math.comb(4 + len(blocks) - 1, 4)
    return {
        "status": "janus-souriau-coadjoint-filtration-order-audit",
        "source_formula": "q'=lambda*mu*q, P'=L P, M'=L M L^T - L P C^T + C P^T L^T",
        "filtration_blocks": blocks,
        "filtration_dimension": sum(row["dimension"] for row in blocks),
        "coadjoint_filtration_derived": True,
        "full_component_order_derived": False,
        "block_profile_levels_on_Sym4": block_profile_levels,
        "orders_1001_states": block_profile_levels == 1001,
        "why_it_fails_full_ordering": (
            "The coadjoint action gives a real triangular block hierarchy q/P/M, "
            "but Lorentz covariance keeps P and M internally degenerate. It does "
            "not derive 11 separate no-carry component weights."
        ),
        "what_it_can_support": [
            "C11 torsor carrier is source-anchored",
            "block hierarchy can constrain any future boundary modular Hamiltonian",
            "full no-carry order must break internal degeneracy by an additional derived boundary structure",
        ],
        "inherits_no_carry_candidate": bridge["no_carry_operator_available_conditionally"],
        "no_fit_closed_now": False,
        "bottom_line": (
            "The published group action improves the story: it supplies a natural "
            "q/P/M filtration. But that filtration gives only 15 degree-4 block "
            "profiles, so it cannot by itself be the 1001-level early-ruler law."
        ),
    }


def isotropy_preserving_anormal_ordering_obstruction_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Check whether a 1001-level A_normal can preserve spatial isotropy."""

    dim_c11 = 11
    degree = 4
    full_levels = math.comb(dim_c11 + degree - 1, degree)
    isotropic_blocks = [
        {"name": "l_triplet", "dimension": 3},
        {"name": "g_triplet", "dimension": 3},
        {"name": "p_triplet", "dimension": 3},
        {"name": "E_scalar", "dimension": 1},
        {"name": "q_scalar", "dimension": 1},
    ]
    block_levels = math.comb(len(isotropic_blocks) + degree - 1, degree)
    return {
        "status": "janus-isotropy-preserving-anormal-ordering-obstruction",
        "requirement": "background A_normal should not pick x/y/z directions inside l,g,p triplets",
        "full_sym4_levels": full_levels,
        "isotropic_block_count": len(isotropic_blocks),
        "isotropic_block_profile_levels": block_levels,
        "orders_1001_while_isotropic": block_levels == full_levels,
        "blocks": isotropic_blocks,
        "consequence": (
            "A diagonal no-carry operator on all 11 components orders 1001 states, "
            "but it breaks spatial isotropy unless the triplet splitting is hidden "
            "inside a gauge/microstate sector that averages out."
        ),
        "allowed_non_rustine_escape_routes": [
            "derive A_normal on isotropic irreducible multiplets, accept at most 70 profiles",
            "derive a non-diagonal SO(3)-invariant operator with simple spectrum on multiplicity spaces",
            "treat no-carry ordering as boundary microstate data and prove isotropic observable averaging",
        ],
        "no_fit_closed_now": False,
        "bottom_line": (
            "The no-carry candidate is mathematically exact but physically expensive. "
            "If the early-ruler Hamiltonian must preserve visible isotropy at the "
            "component level, the 1001-level ordering is blocked."
        ),
    }


def boundary_microstate_isotropic_average_candidate_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Try to keep 1001 boundary microstates while preserving macroscopic isotropy."""

    obstruction = isotropy_preserving_anormal_ordering_obstruction_payload(target_redshift)
    N_micro = obstruction["full_sym4_levels"]
    N_macro = obstruction["isotropic_block_profile_levels"]
    return {
        "status": "janus-boundary-microstate-isotropic-average-candidate",
        "proposal": (
            "Use all Sym4(C11) occupation states as boundary microstates, but require "
            "observable stress/ruler tensors to be SO(3)-averages over l,g,p triplets."
        ),
        "counts": {
            "microstate_count": N_micro,
            "macro_isotropic_profile_count": N_macro,
            "microstates_reach_pre_drag": N_micro - 1.0 >= target_redshift,
            "macro_profiles_reach_pre_drag": N_macro - 1.0 >= target_redshift,
        },
        "what_this_would_fix": {
            "keeps_1001_hidden_boundary_states": True,
            "does_not_pick_visible_xyz_direction": True,
            "can_preserve_background_isotropy": True,
        },
        "hard_conditions": {
            "boundary_density_matrix_SO3_invariant": False,
            "visible_observables_depend_only_on_triplet_averages": False,
            "early_ruler_uses_microstate_count_not_macro_profiles": False,
            "no_carry_Hamiltonian_commutes_with_visible_SO3_after_averaging": False,
        },
        "failure_if_conditions_not_derived": (
            "Either the 1001 ordering breaks visible isotropy, or the isotropic "
            "projection collapses the usable ruler count back to 70."
        ),
        "no_fit_closed_now": False,
        "bottom_line": (
            "This is the best non-circular interpretation of the no-carry idea: "
            "1001 is a hidden boundary microstate count, while visible cosmology "
            "sees only SO(3)-averaged tensors. It still needs a derived invariant "
            "boundary state law and a proof that the ruler uses microstates."
        ),
    }


def microcanonical_boundary_state_law_attempt_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Attempt the minimal SO(3)-invariant boundary state: rho = I / dim(H)."""

    candidate = boundary_microstate_isotropic_average_candidate_payload(target_redshift)
    N = candidate["counts"]["microstate_count"]
    entropy_nats = math.log(N)
    entropy_bits = math.log2(N)
    return {
        "status": "janus-microcanonical-boundary-state-law-attempt",
        "state_law_candidate": "rho_boundary = Identity_on_Sym4(C11) / 1001",
        "symmetry": {
            "SO3_invariant": True,
            "PT_invariant_if_sector_is_PT_closed": True,
            "selects_visible_xyz_direction": False,
        },
        "entropy": {
            "dim_H_boundary": N,
            "S_boundary_nats": entropy_nats,
            "S_boundary_bits": entropy_bits,
        },
        "ruler_map_attempt": {
            "a_min_candidate": 1.0 / N,
            "z_max_candidate": N - 1.0,
            "pre_drag_reach": N - 1.0 >= target_redshift,
            "uses_microstate_count": True,
            "derives_ruler_from_entropy": False,
        },
        "what_it_closes": {
            "boundary_density_matrix_SO3_invariant": True,
            "visible_preferred_direction_avoided": True,
            "hidden_microstate_count_1001": True,
        },
        "remaining_derivation_gap": [
            "derive why the Janus/PT boundary chooses the maximally mixed state",
            "derive why the early ruler resolution is a_min = exp(-S_boundary)",
            "derive coupling between this boundary entropy and photon-baryon drag/ruler",
        ],
        "no_fit_closed_now": False,
        "bottom_line": (
            "The microcanonical state is the cleanest isotropic use of the 1001 "
            "states. It closes the isotropy problem, but not yet the physics of "
            "why boundary entropy sets the early-ruler cutoff."
        ),
    }


def entropy_to_ruler_resolution_map_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Reduce boundary entropy to a minimal dimensionless resolution cell."""

    state = microcanonical_boundary_state_law_attempt_payload(target_redshift)
    N = state["entropy"]["dim_H_boundary"]
    a_min = math.exp(-state["entropy"]["S_boundary_nats"])
    z_max = float(N - 1)
    return {
        "status": "janus-entropy-to-ruler-resolution-map",
        "input_state": "microcanonical Sym4(C11) boundary state",
        "mathematical_map": {
            "N_cells": N,
            "S_boundary": state["entropy"]["S_boundary_nats"],
            "a_min_equals_exp_minus_S": abs(a_min - 1.0 / N) < 1e-15,
            "a_min": a_min,
            "z_max": z_max,
            "pre_drag_reach": z_max >= target_redshift,
        },
        "interpretation": (
            "A finite boundary Hilbert sector with N orthogonal microstates gives "
            "a dimensionless resolution cell 1/N if the throat/ruler coordinate "
            "is resolved by boundary states."
        ),
        "what_is_closed": {
            "entropy_cell_count_to_dimensionless_resolution": True,
            "a_min_from_boundary_entropy_math": True,
            "z_max_reaches_1000_for_N1001": True,
        },
        "what_is_not_closed": {
            "Janus_action_derives_boundary_state_resolution_of_scale_factor": False,
            "photon_baryon_drag_uses_this_resolution": False,
            "native_sound_horizon_integral_executable": False,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The entropy-to-resolution map is mathematically clean. The remaining "
            "physics is to derive that Janus photon-baryon drag is cut off by this "
            "boundary resolution, rather than by an independent early-time branch."
        ),
    }


def entropy_cutoff_to_native_sound_horizon_bridge_payload(
    target_redshift: float = 1000.0,
) -> dict:
    """Attach the entropy-derived a_min to the native sound-horizon contract."""

    resolution = entropy_to_ruler_resolution_map_payload(target_redshift)
    sound = native_sound_horizon_integral_contract_payload()
    a_min = resolution["mathematical_map"]["a_min"]
    z_max = resolution["mathematical_map"]["z_max"]
    rows = []
    for row in sound["candidate_H_scalings"]:
        rows.append(
            {
                **row,
                "finite_with_entropy_cutoff": True,
                "lower_bound_used": a_min,
            }
        )
    return {
        "status": "janus-entropy-cutoff-to-native-sound-horizon-bridge",
        "entropy_cutoff": {
            "a_min": a_min,
            "z_max": z_max,
            "pre_drag_reach": resolution["mathematical_map"]["pre_drag_reach"],
        },
        "sound_horizon_contract_updated": {
            "r_d_integral": sound["sound_speed_contract"]["r_d_integral"],
            "zero_lower_limit_divergence_avoided": True,
            "active_lower_bound_supplied_conditionally": True,
        },
        "candidate_H_scalings": rows,
        "remaining_inputs_after_cutoff": {
            "derive_entropy_cutoff_from_Janus_action": False,
            "derive_drag_epoch_a_d": False,
            "derive_H_J_of_a": False,
            "derive_R_b0_or_baryon_photon_normalization": False,
        },
        "no_fit_closed_now": False,
        "bottom_line": (
            "The entropy cutoff would remove the lower-limit obstruction in the "
            "native sound-horizon contract and reaches z=1000. It still does not "
            "make BAO executable because the drag surface, H_J(a), and baryon/"
            "photon normalization remain uncomputed from Janus."
        ),
    }


def entropy_cutoff_drag_readiness_audit_payload(
    root: Path | str = Path("."),
    target_redshift: float = 1000.0,
) -> dict:
    """Audit which native drag inputs remain after the entropy cutoff."""

    root = Path(root)
    active = root / "outputs" / "active_z2_sigma"
    cutoff = entropy_cutoff_to_native_sound_horizon_bridge_payload(target_redshift)
    constants = _read_json_if_present(active / "early_plasma_codata_constants_inputs.json")
    temp = _read_json_if_present(active / "early_plasma_photon_temperature_firas_inputs.json")
    photon = _read_json_if_present(active / "early_plasma_photon_density_firas_codata_inputs.json")
    baryon_files = list(active.glob("*baryon*"))
    hubble_files = list(active.glob("*hubble*"))

    C_ion = None
    if constants and temp:
        E_ion = constants["constants"]["hydrogen_ionization_energy_J"]
        k_B = constants["constants"]["boltzmann_constant_J_K"]
        T0 = temp["normalizations"]["photon_temperature0_Z2Sigma"]
        C_ion = E_ion / (k_B * T0)

    return {
        "status": "janus-entropy-cutoff-drag-readiness-audit",
        "entropy_cutoff_available": cutoff["sound_horizon_contract_updated"]["active_lower_bound_supplied_conditionally"],
        "C_ion_from_CODATA_FIRAS": C_ion,
        "available_inputs": {
            "codata_constants": constants is not None,
            "FIRAS_photon_temperature": temp is not None,
            "FIRAS_photon_density": photon is not None,
            "baryon_related_active_files": [p.name for p in baryon_files],
            "hubble_related_active_files": [p.name for p in hubble_files],
        },
        "closed_or_conditionally_closed": {
            "a_min": True,
            "C_ion_numeric_from_direct_temperature": C_ion is not None,
            "photon_density_normalization": photon is not None,
        },
        "still_missing_for_drag_epoch": {
            "baryon_number_or_eta_b_normalization": len(baryon_files) == 0,
            "native_H_J_of_a": len(hubble_files) == 0,
            "A_drag_normalization": True,
        },
        "drag_prediction_executable": False,
        "no_fit_closed_now": False,
        "bottom_line": (
            "After the entropy cutoff, the active files can supply photon/CODATA "
            "pieces and a numeric C_ion from FIRAS temperature. The drag epoch is "
            "still not executable because no active baryon normalization or native "
            "H_J(a) is present."
        ),
    }


def entropy_cutoff_exact_shape_compatibility_payload(
    late_q0: float = -0.087,
    target_redshift: float = 1000.0,
) -> dict:
    """Check whether the entropy cutoff can live on the same exact SN branch."""

    cutoff = entropy_to_ruler_resolution_map_payload(target_redshift)
    z_entropy = cutoff["mathematical_map"]["z_max"]
    q0_required = -1.0 / (2.0 * z_entropy)
    late_shape = exact_shape_throat_lower_bound_payload(late_q0)
    return {
        "status": "janus-entropy-cutoff-exact-shape-compatibility",
        "same_exact_shape_relation": "z_max = -1/(2*q0)",
        "entropy_cutoff_branch": {
            "z_max": z_entropy,
            "q0_required_if_same_shape": q0_required,
        },
        "published_late_SN_branch": {
            "q0": late_q0,
            "z_max": late_shape["z_max"],
            "a_min": late_shape["a_min_over_a0"],
        },
        "same_branch_compatible": abs(q0_required - late_q0) < 1e-6,
        "interpretation": (
            "The entropy cutoff cannot simply replace the late exact SN throat "
            "inside one cosh^2 branch. It requires either an attached early branch "
            "or a modified early redshift/scale map."
        ),
        "next_required": [
            "derive early-to-late matching surface",
            "derive H_J(a) on the entropy-cutoff early branch",
            "preserve the published late SN q0 branch after matching",
        ],
        "no_fit_closed_now": False,
        "bottom_line": (
            "The entropy cutoff fixes the pre-drag reach but is incompatible with "
            "using the same exact late SN cosh branch. The model needs a native "
            "early branch glued to the late Janus branch."
        ),
    }


def two_cosh_branch_matching_obstruction_payload(
    late_q0: float = -0.087,
    target_redshift: float = 1000.0,
) -> dict:
    """Check C1 matching if the entropy early branch and late SN branch are both cosh^2."""

    compatibility = entropy_cutoff_exact_shape_compatibility_payload(late_q0, target_redshift)
    a_early_min = 1.0 / (1.0 + compatibility["entropy_cutoff_branch"]["z_max"])
    a_late_min = compatibility["published_late_SN_branch"]["a_min"]
    ratio = a_late_min / a_early_min
    u_early_at_late_min = math.acosh(math.sqrt(ratio))
    h_shape_early = 2.0 * math.tanh(u_early_at_late_min)
    h_shape_late_at_throat = 0.0
    return {
        "status": "janus-two-cosh-branch-matching-obstruction",
        "assumption_tested": "early and late branches both use a=a_min*cosh(u)^2 and match at the late branch throat",
        "early_branch": {
            "a_min": a_early_min,
            "z_max": compatibility["entropy_cutoff_branch"]["z_max"],
        },
        "late_branch": compatibility["published_late_SN_branch"],
        "matching_at_late_throat": {
            "a_match": a_late_min,
            "early_u_at_match": u_early_at_late_min,
            "early_shape_H_over_du": h_shape_early,
            "late_shape_H_over_du": h_shape_late_at_throat,
            "C0_scale_factor_match_possible": True,
            "C1_shape_match_possible_without_extra_lapse_or_surface": abs(h_shape_early) < 1e-12,
        },
        "interpretation": (
            "A pure two-cosh gluing at the late throat is not smooth: the late "
            "branch has zero shape velocity at its throat, while the entropy "
            "early branch reaches that scale with nonzero shape velocity."
        ),
        "non_rustine_escape_routes": [
            "derive a non-cosh early branch from the native plasma/boundary action",
            "match away from the late throat and re-derive the late-domain map",
            "derive a physical transition surface carrying the C1 jump",
            "derive a lapse/time reparametrization from the bimetric action that equalizes H",
        ],
        "no_fit_closed_now": False,
        "bottom_line": (
            "The entropy early branch cannot be glued to the published late branch "
            "by simply placing two exact cosh solutions back-to-back at the late "
            "throat. A real early-branch dynamics or transition law is required."
        ),
    }


def current_branch_early_late_matching_final_pass_payload(
    late_q0: float = -0.087,
    target_redshift: float = 1000.0,
) -> dict:
    """Final non-rustine matching pass for the current entropy/throat branch."""

    cutoff = entropy_cutoff_to_native_sound_horizon_bridge_payload(target_redshift)
    drag = entropy_cutoff_drag_readiness_audit_payload(target_redshift=target_redshift)
    compatibility = entropy_cutoff_exact_shape_compatibility_payload(late_q0, target_redshift)
    two_cosh = two_cosh_branch_matching_obstruction_payload(late_q0, target_redshift)
    routes = [
        {
            "name": "same_late_cosh_branch",
            "closed": compatibility["same_branch_compatible"],
            "failure": "entropy cutoff requires q0=-0.0005, not the published late q0=-0.087",
        },
        {
            "name": "two_cosh_gluing_at_late_throat",
            "closed": two_cosh["matching_at_late_throat"]["C1_shape_match_possible_without_extra_lapse_or_surface"],
            "failure": "C1 mismatch: early branch has nonzero shape velocity at the late throat scale",
        },
        {
            "name": "entropy_cutoff_sound_horizon",
            "closed": False,
            "progress": cutoff["sound_horizon_contract_updated"]["zero_lower_limit_divergence_avoided"],
            "failure": "a_min is supplied conditionally, but H_J(a), a_d, and R_b0 are not",
        },
        {
            "name": "native_drag_epoch",
            "closed": drag["drag_prediction_executable"],
            "progress": drag["closed_or_conditionally_closed"],
            "failure": "active baryon normalization and native H_J(a) are absent",
        },
        {
            "name": "transition_surface_or_lapse",
            "closed": False,
            "failure": "no action-derived surface stress, lapse law, or C1 jump law exists in this branch",
        },
    ]
    return {
        "status": "janus-current-branch-early-late-matching-final-pass",
        "routes": routes,
        "closed_now": any(row["closed"] is True for row in routes),
        "what_is_genuinely_progressed": [
            "hidden 1001 microstate count can be isotropic via microcanonical state",
            "a_min=1/1001 gives z_max=1000 and regularizes the sound-horizon lower limit",
            "C_ion is available from CODATA/FIRAS",
        ],
        "hard_blockers_remaining": [
            "derive early H_J(a)",
            "derive baryon/eta_b normalization",
            "derive transition surface or lapse matching law",
            "preserve published late SN q0 branch",
        ],
        "recommended_next_branch": "JanusProjectivePointPTLimit",
        "no_fit_closed_now": False,
        "bottom_line": (
            "The current throat/entropy branch has been pushed to the non-rustine "
            "boundary. It supplies a plausible early cutoff, but cannot close an "
            "early-to-late match without a new transition law or early dynamics."
        ),
    }


def projective_point_pt_limit_opening_payload() -> dict:
    """Open the no-throat projective point PT limit."""

    return {
        "status": "janus-projective-point-pt-limit-opening",
        "active_geometry": {
            "global_cover": "S4_L -> RP4_L",
            "PT_identification": "antipodal projective point",
            "finite_throat_sigma": False,
            "surface_stress_sigma": False,
            "normal_connection_sigma": False,
        },
        "removed_obligations": [
            "R_Sigma selection",
            "Sigma boundary state law",
            "omega_perp/rho_perp/A_normal from throat collar",
            "C1 gluing across finite throat",
        ],
        "new_or_remaining_obligations": [
            "singular/projective initial condition",
            "distributional or limiting field equations at the PT point",
            "early redshift/history map without throat radius",
            "native BAO/CMB ruler if observations are targeted",
        ],
        "expected_use": (
            "Reference-minimal Janus branch: faithful to projective topology and "
            "useful for seeing which problems were artifacts of finite-throat resolution."
        ),
        "no_fit_closed_now": False,
        "bottom_line": (
            "The point PT limit removes most Sigma-specific blockers, but it also "
            "removes the boundary microphysics that supplied a_min. It is cleaner "
            "geometrically and less predictive for early rulers unless a singular "
            "initial law is derived."
        ),
    }


def non_throat_pt_transition_candidate_matrix_payload() -> dict:
    """Compare non-gorge, non-point PT transition candidates."""

    candidates = [
        {
            "name": "ConformalPTBoundary",
            "geometry": "degenerate/finite conformal boundary with PT identification",
            "avoids_sigma_radius": True,
            "keeps_nontrivial_transition": True,
            "main_strength": "can preserve finite conformal data while physical volume tends to zero",
            "main_blocker": "derive conformal matching law and physical redshift map",
            "priority": 1,
        },
        {
            "name": "CrosscapPTTransition",
            "geometry": "non-orientable local projective/crosscap transition",
            "avoids_sigma_radius": True,
            "keeps_nontrivial_transition": True,
            "main_strength": "topological PT action without a round throat modulus",
            "main_blocker": "derive field equations/holonomy without introducing hidden surface stress",
            "priority": 2,
        },
        {
            "name": "NullPTBoundary",
            "geometry": "lightlike PT junction",
            "avoids_sigma_radius": True,
            "keeps_nontrivial_transition": True,
            "main_strength": "no spacelike throat radius; causal bridge structure",
            "main_blocker": "requires null charge/tension or null boundary condition",
            "priority": 3,
        },
    ]
    return {
        "status": "janus-non-throat-pt-transition-candidate-matrix",
        "candidates": candidates,
        "recommended_first": "ConformalPTBoundary",
        "why": (
            "It is the best compromise between the point limit and a finite throat: "
            "no Sigma radius, but still enough boundary structure to carry matching data."
        ),
        "first_test_contract": [
            "define conformal boundary metric class [h]",
            "derive PT action on [h] and matter/energy signs",
            "derive conformal redshift map",
            "check whether late SN branch can attach without C1 throat mismatch",
        ],
        "no_fit_closed_now": False,
        "bottom_line": (
            "Among non-throat alternatives, ConformalPTBoundary is the most promising. "
            "Crosscap is topologically interesting, but likely harder to make dynamical."
        ),
    }


def conformal_pt_boundary_matching_attempt_payload(
    late_q0: float = -0.087,
    target_redshift: float = 1000.0,
) -> dict:
    """Push the ConformalPTBoundary route to its current non-rustine frontier."""

    required_q0_same_cosh = -1.0 / (2.0 * target_redshift)
    same_late_shape_compatible = abs(late_q0 - required_q0_same_cosh) < 1e-12
    checks = {
        "finite_sigma_radius_removed": True,
        "c1_throat_velocity_mismatch_removed": True,
        "conformal_boundary_class_declared": True,
        "pt_action_on_conformal_class_declared": True,
        "redshift_can_be_formulated_conformally": True,
        "conformal_lapse_or_clock_law_derived": False,
        "native_early_HJ_derived": False,
        "baryon_eta_normalization_derived": False,
        "same_late_cosh_shape_compatible": same_late_shape_compatible,
    }
    return {
        "status": "janus-conformal-pt-boundary-matching-attempt",
        "candidate": "ConformalPTBoundary",
        "late_q0": late_q0,
        "target_redshift": target_redshift,
        "required_q0_if_same_late_cosh_branch": required_q0_same_cosh,
        "checks": checks,
        "closed_now": all(checks.values()),
        "what_it_fixes": [
            "removes finite Sigma radius selection",
            "removes C1 mismatch caused specifically by finite-throat gluing",
            "keeps finite conformal boundary data instead of collapsing to a bare point",
        ],
        "what_still_blocks": [
            "derive the conformal lapse/clock law",
            "derive native early H_J(a) in the conformal frame",
            "derive active baryon/photon normalization",
            "show how the published late SN branch attaches without reverting to the same cosh q0 constraint",
        ],
        "bottom_line": (
            "ConformalPTBoundary is the strongest non-throat candidate so far. "
            "It removes the finite-throat obstruction, but it does not by itself "
            "derive the early clock/ruler needed for BAO or CMB."
        ),
    }


def crosscap_pt_transition_obstruction_payload() -> dict:
    """Push the CrosscapPTTransition route to its current frontier."""

    checks = {
        "sigma_radius_removed": True,
        "nonorientable_pt_transition_declared": True,
        "topological_z2_action_available": True,
        "local_field_equations_on_crosscap_derived": False,
        "stress_free_transition_proved": False,
        "redshift_or_clock_law_derived": False,
        "ruler_contract_derived": False,
    }
    return {
        "status": "janus-crosscap-pt-transition-obstruction",
        "candidate": "CrosscapPTTransition",
        "checks": checks,
        "closed_now": all(checks.values()),
        "strength": (
            "A crosscap gives a clean projective/non-orientable PT action without "
            "a round throat modulus."
        ),
        "obstruction": (
            "Topology alone does not provide the local dynamical matching law. "
            "Without a derived stress-free condition or action principle on the "
            "crosscap, it cannot supply H_J(a), redshift, or a ruler."
        ),
        "bottom_line": (
            "Crosscap is a good topology candidate, but weaker than ConformalPTBoundary "
            "for executable cosmology because the local dynamics are currently absent."
        ),
    }


def exotic_pt_transition_configuration_matrix_payload() -> dict:
    """Rank more speculative non-throat transition geometries."""

    candidates = [
        {
            "name": "WeylCuspPTBoundary",
            "idea": "physical volume shrinks while conformal boundary data stay finite",
            "new_scale_risk": "low",
            "dynamic_path": "derive Weyl/lapse boundary flow",
            "rank": 1,
        },
        {
            "name": "MobiusNormalBand",
            "idea": "PT acts as a twisted normal line bundle rather than a round throat",
            "new_scale_risk": "medium",
            "dynamic_path": "derive normal holonomy and show it induces a clock/ruler",
            "rank": 2,
        },
        {
            "name": "CrosscapPTTransition",
            "idea": "local projective crosscap replacing Sigma",
            "new_scale_risk": "medium",
            "dynamic_path": "derive crosscap field equations without hidden surface stress",
            "rank": 3,
        },
        {
            "name": "LensSpacePTQuotient",
            "idea": "replace RP3-like slice by a finite quotient carrying discrete cycles",
            "new_scale_risk": "high",
            "dynamic_path": "derive why this quotient is Janus-native and fixes a ruler",
            "rank": 4,
        },
        {
            "name": "BranchedCoverPTTransition",
            "idea": "allow a controlled branch locus instead of a throat",
            "new_scale_risk": "high",
            "dynamic_path": "derive branch stress/defect cancellation from the action",
            "rank": 5,
        },
    ]
    return {
        "status": "janus-exotic-pt-transition-configuration-matrix",
        "candidates": candidates,
        "recommended_next": "WeylCuspPTBoundary",
        "why": (
            "It is effectively the sharper version of ConformalPTBoundary: no "
            "finite throat radius, but enough conformal data to try deriving an "
            "early clock."
        ),
        "not_recommended_now": [
            "LensSpacePTQuotient: likely adds topology not present in Janus unless derived",
            "BranchedCoverPTTransition: likely reintroduces defect stress",
        ],
        "bottom_line": (
            "The useful exotic direction is not arbitrary topology; it is a conformal/"
            "Weyl boundary transition where the scale can emerge from clock flow, not "
            "from a finite Sigma radius."
        ),
    }


def weyl_cusp_pt_boundary_clock_route_payload() -> dict:
    """Evaluate the Weyl-cusp sharpening of ConformalPTBoundary."""

    checks = {
        "finite_sigma_radius_removed": True,
        "physical_volume_can_vanish": True,
        "conformal_boundary_data_finite": True,
        "redshift_domain_can_reach_pre_drag": True,
        "late_cosh_zmax_obstruction_removed": True,
        "weyl_gauge_fixed_by_action_or_matter_clock": False,
        "physical_clock_law_derived": False,
        "conformal_friedmann_equation_derived": False,
        "late_SN_matching_law_derived": False,
        "native_baryon_photon_normalization_derived": False,
    }
    return {
        "status": "janus-weyl-cusp-pt-boundary-clock-route",
        "candidate": "WeylCuspPTBoundary",
        "ansatz": {
            "physical_metric": "g = Omega^2 * g_hat",
            "pt_boundary": "Omega -> 0 with finite conformal data [g_hat]",
            "interpretation": "infinite early redshift from conformal scale collapse, not finite throat radius",
        },
        "checks": checks,
        "domain_problem_solved": (
            checks["redshift_domain_can_reach_pre_drag"]
            and checks["late_cosh_zmax_obstruction_removed"]
        ),
        "dynamics_problem_solved": all(
            checks[key]
            for key in [
                "weyl_gauge_fixed_by_action_or_matter_clock",
                "physical_clock_law_derived",
                "conformal_friedmann_equation_derived",
                "late_SN_matching_law_derived",
            ]
        ),
        "closed_now": all(checks.values()),
        "what_it_really_changes": [
            "early z~1000 no longer needs q0=-0.0005 on the late SN cosh branch",
            "the transition is controlled by conformal scale collapse rather than R_Sigma",
            "the old finite-throat C1 mismatch is avoided rather than patched",
        ],
        "hard_blocker": (
            "A Weyl cusp is gauge until the model derives which conformal frame is "
            "physical for matter clocks. Without that, Omega(a) is not an observable "
            "H_J(a) and cannot generate BAO/CMB rulers."
        ),
        "next_required_calculation": [
            "derive Weyl-frame matter coupling from the Janus action",
            "derive physical clock/lapse from that coupling",
            "derive conformal Friedmann equation for Omega",
            "derive matching law from the Weyl cusp to the published late SN branch",
        ],
        "bottom_line": (
            "WeylCuspPTBoundary is the first non-throat route that genuinely removes "
            "the early-redshift domain obstruction. It still needs a physical Weyl "
            "frame/clock law before it becomes predictive."
        ),
    }


def weyl_cusp_physical_clock_candidate_matrix_payload() -> dict:
    """Rank non-rustine ways to make the Weyl cusp clock physical."""

    candidates = [
        {
            "name": "VisibleMatterJordanFrame",
            "janus_native": True,
            "fixes_weyl_gauge_conditionally": True,
            "requires_new_field": False,
            "missing": "explicit paper-native action/pullback showing visible matter couples to g=Omega^2*g_hat through the cusp",
            "rank": 1,
        },
        {
            "name": "BimetricScaleRatioClock",
            "janus_native": True,
            "fixes_weyl_gauge_conditionally": True,
            "requires_new_field": False,
            "missing": "derive Omega from a_plus/a_minus or determinant ratio in the published bimetric equations",
            "rank": 2,
        },
        {
            "name": "ThermalPhotonClock",
            "janus_native": "partial",
            "fixes_weyl_gauge_conditionally": True,
            "requires_new_field": False,
            "missing": "derive entropy/temperature transport and baryon-photon normalization, not just use FIRAS",
            "rank": 3,
        },
        {
            "name": "DilatonCompensatorClock",
            "janus_native": False,
            "fixes_weyl_gauge_conditionally": True,
            "requires_new_field": True,
            "missing": "new compensator action and potential",
            "rank": 4,
        },
        {
            "name": "PureConformalGeometryClock",
            "janus_native": False,
            "fixes_weyl_gauge_conditionally": False,
            "requires_new_field": False,
            "missing": "pure conformal class has no physical clock by itself",
            "rank": 5,
        },
    ]
    return {
        "status": "janus-weyl-cusp-physical-clock-candidate-matrix",
        "candidates": candidates,
        "recommended_next": "VisibleMatterJordanFrame",
        "secondary_next": "BimetricScaleRatioClock",
        "rejected_as_pure_geometry": "PureConformalGeometryClock",
        "extension_only": "DilatonCompensatorClock",
        "bottom_line": (
            "The Weyl cusp can become physical only through matter coupling or "
            "bimetric scale-ratio dynamics. Pure topology/conformal geometry is not "
            "enough because the conformal factor is gauge without a clock."
        ),
    }


def visible_matter_jordan_frame_pullback_attempt_payload() -> dict:
    """Use the published two-geodesic rule to test the visible matter clock route."""

    checks = {
        "published_positive_sector_geodesic_rule_available": True,
        "visible_photons_follow_g_plus": True,
        "visible_matter_clock_fixed_by_g_plus": True,
        "weyl_gauge_fixed_for_visible_observers": True,
        "g_plus_pullback_to_weyl_cusp_derived": False,
        "omega_evolution_from_bimetric_equations_derived": False,
        "redshift_map_through_pt_boundary_derived": False,
        "late_sn_branch_matching_derived": False,
    }
    return {
        "status": "janus-visible-matter-jordan-frame-pullback-attempt",
        "source_anchors": [
            "M15/M30: positive photons and positive masses follow the g(+) geodesic family",
            "M15/M30: negative sector follows its own g(-) geodesic family",
        ],
        "checks": checks,
        "visible_clock_fixed": (
            checks["visible_matter_clock_fixed_by_g_plus"]
            and checks["weyl_gauge_fixed_for_visible_observers"]
        ),
        "weyl_cusp_predictive": all(
            checks[key]
            for key in [
                "g_plus_pullback_to_weyl_cusp_derived",
                "omega_evolution_from_bimetric_equations_derived",
                "redshift_map_through_pt_boundary_derived",
                "late_sn_branch_matching_derived",
            ]
        ),
        "closed_now": all(checks.values()),
        "bottom_line": (
            "The published bimetric/geodesic rule fixes the visible physical clock "
            "as the g(+) Jordan frame. It does not yet derive how g(+) pulls back "
            "through a Weyl cusp/PT boundary or how Omega evolves there."
        ),
    }


def bimetric_scale_ratio_clock_attempt_payload() -> dict:
    """Test whether the two scale factors can define the Weyl-cusp clock."""

    checks = {
        "two_scale_factors_available": True,
        "published_ratio_signal_available": True,
        "determinant_ratio_field_equations_available": True,
        "omega_defined_as_bimetric_ratio": False,
        "ratio_evolution_through_pre_drag_derived": False,
        "ratio_selects_physical_visible_clock": False,
        "matches_late_sn_branch_without_extra_law": False,
    }
    return {
        "status": "janus-bimetric-scale-ratio-clock-attempt",
        "candidate_definitions_tested": [
            "Omega = a_plus / a_minus",
            "Omega = a_minus / a_plus",
            "Omega from determinant ratio sqrt(-g_minus / -g_plus)",
        ],
        "checks": checks,
        "closed_now": all(checks.values()),
        "why_not_closed": (
            "The bimetric equations contain determinant-ratio coupling and the "
            "literature gives scale-factor ratio signals, but no source currently "
            "derives a unique Weyl-cusp Omega or its pre-drag evolution."
        ),
        "bottom_line": (
            "Bimetric scale ratio remains the best Janus-native clock route after "
            "the visible Jordan frame, but it needs an explicit ratio evolution law."
        ),
    }


def gplus_weyl_cusp_kinematic_pullback_payload() -> dict:
    """Close the kinematic pullback of visible g(+) through a Weyl cusp."""

    checks = {
        "g_plus_conformal_decomposition_declared": True,
        "visible_proper_time_relation_declared": True,
        "visible_scale_factor_relation_declared": True,
        "visible_redshift_relation_declared": True,
        "visible_hubble_relation_declared": True,
        "pt_cusp_redshift_domain_available": True,
        "omega_dynamics_derived": False,
        "source_terms_in_conformal_frame_derived": False,
    }
    formulas = {
        "metric": "g_plus = Omega^2 * g_hat_plus",
        "proper_time": "d tau_plus = Omega * d tau_hat",
        "scale_factor": "a_plus = Omega * a_hat",
        "redshift": "1+z = (Omega_obs*a_hat_obs)/(Omega_emit*a_hat_emit)",
        "hubble": "H_plus = Omega^-1 * (H_hat + d ln(Omega)/d tau_hat)",
    }
    return {
        "status": "janus-gplus-weyl-cusp-kinematic-pullback",
        "checks": checks,
        "formulas": formulas,
        "kinematic_pullback_closed": all(
            checks[key]
            for key in [
                "g_plus_conformal_decomposition_declared",
                "visible_proper_time_relation_declared",
                "visible_scale_factor_relation_declared",
                "visible_redshift_relation_declared",
                "visible_hubble_relation_declared",
                "pt_cusp_redshift_domain_available",
            ]
        ),
        "predictive_dynamics_closed": (
            checks["omega_dynamics_derived"]
            and checks["source_terms_in_conformal_frame_derived"]
        ),
        "bottom_line": (
            "The visible g(+) Weyl-cusp pullback is kinematically closed. This is "
            "not yet a prediction because Omega(t) and the conformal-frame sources "
            "are not derived."
        ),
    }


def conformal_friedmann_omega_equation_contract_payload() -> dict:
    """Write the minimal equation contract needed to make Omega dynamical."""

    checks = {
        "kinematic_pullback_available": True,
        "conformal_friedmann_identity_declared": True,
        "omega_first_order_equation_form_declared": True,
        "requires_hat_background_declared": True,
        "requires_effective_density_declared": True,
        "hat_background_derived": False,
        "effective_density_derived": False,
        "initial_or_boundary_condition_for_omega_derived": False,
    }
    return {
        "status": "janus-conformal-friedmann-omega-equation-contract",
        "equation_contract": {
            "a_plus": "Omega * a_hat",
            "H_plus": "Omega^-1 * (H_hat + d ln(Omega)/d tau_hat)",
            "friedmann_plus": "H_plus^2 + k/a_plus^2 = kappa_eff*rho_eff_plus/3",
            "omega_equation": "(H_hat + d ln(Omega)/d tau_hat)^2 + k/a_hat^2 = Omega^2*kappa_eff*rho_eff_plus/3",
        },
        "checks": checks,
        "equation_contract_closed": all(
            checks[key]
            for key in [
                "kinematic_pullback_available",
                "conformal_friedmann_identity_declared",
                "omega_first_order_equation_form_declared",
                "requires_hat_background_declared",
                "requires_effective_density_declared",
            ]
        ),
        "omega_solution_closed": (
            checks["hat_background_derived"]
            and checks["effective_density_derived"]
            and checks["initial_or_boundary_condition_for_omega_derived"]
        ),
        "bottom_line": (
            "The Omega equation can be written without a throat radius. To solve it, "
            "the branch still needs a conformal background, effective source, and "
            "boundary/initial condition derived from Janus."
        ),
    }


def omega_dynamics_candidate_matrix_payload() -> dict:
    """Rank possible non-rustine sources for Omega dynamics."""

    candidates = [
        {
            "name": "ConformalEinsteinTrace",
            "rank": 1,
            "needs_new_field": False,
            "route": "derive Omega from the trace/00 projection of G[g_plus]=source after g_plus=Omega^2*g_hat",
            "blocker": "requires active conformal background and rho_eff_plus",
        },
        {
            "name": "BimetricDeterminantRatio",
            "rank": 2,
            "needs_new_field": False,
            "route": "derive Omega from sqrt(-g_minus/-g_plus) coupling in the Janus field equations",
            "blocker": "requires proving the two metrics are conformally related near PT or deriving a unique ratio map",
        },
        {
            "name": "VisibleMatterConservation",
            "rank": 3,
            "needs_new_field": False,
            "route": "derive Omega from conservation of visible radiation/matter in the g(+) Jordan frame",
            "blocker": "gives rho(a_plus), not Omega relative to a_hat unless a_hat is fixed",
        },
        {
            "name": "VariableConstantsClock",
            "rank": 4,
            "needs_new_field": False,
            "route": "use published variable-constants scaling to define the pre-drag clock",
            "blocker": "must be tied to the Weyl cusp rather than inserted as an independent clock",
        },
        {
            "name": "DilatonCompensator",
            "rank": 5,
            "needs_new_field": True,
            "route": "add a scalar compensator whose vev is Omega",
            "blocker": "extension, not paper-native/no-rustine",
        },
    ]
    return {
        "status": "janus-omega-dynamics-candidate-matrix",
        "candidates": candidates,
        "recommended_next": "ConformalEinsteinTrace",
        "secondary_next": "BimetricDeterminantRatio",
        "bottom_line": (
            "The cleanest next calculation is the conformal Einstein trace/00 "
            "reduction. It keeps the route geometric and uses g(+) rather than "
            "adding a new scalar."
        ),
    }


def conformal_einstein_trace_reduction_payload() -> dict:
    """Derive the symbolic trace reduction for Omega in 4D."""

    checks = {
        "conformal_transform_formula_declared": True,
        "phi_defined_as_log_omega": True,
        "trace_equation_declared": True,
        "omega_second_order_equation_declared": True,
        "no_new_scalar_field_added": True,
        "hat_curvature_source_derived": False,
        "trace_stress_source_derived": False,
        "boundary_condition_derived": False,
    }
    return {
        "status": "janus-conformal-einstein-trace-reduction",
        "definitions": {
            "metric": "g_plus = exp(2 phi) * g_hat_plus",
            "omega": "Omega = exp(phi)",
        },
        "trace_reduction": {
            "ricci_scalar": "R[g_plus] = exp(-2 phi) * (R_hat - 6 box_hat(phi) - 6 |grad_hat phi|^2)",
            "einstein_trace": "-R[g_plus] = kappa_eff * T_eff_plus",
            "omega_equation": "R_hat - 6 box_hat(phi) - 6 |grad_hat phi|^2 = -kappa_eff * exp(2 phi) * T_eff_plus",
        },
        "checks": checks,
        "symbolic_reduction_closed": all(
            checks[key]
            for key in [
                "conformal_transform_formula_declared",
                "phi_defined_as_log_omega",
                "trace_equation_declared",
                "omega_second_order_equation_declared",
                "no_new_scalar_field_added",
            ]
        ),
        "active_solution_closed": (
            checks["hat_curvature_source_derived"]
            and checks["trace_stress_source_derived"]
            and checks["boundary_condition_derived"]
        ),
        "bottom_line": (
            "The conformal trace route gives a real Omega equation without adding "
            "a dilaton. It is blocked only at active Janus data: R_hat, T_eff_plus, "
            "and a PT/late boundary condition."
        ),
    }


def determinant_ratio_to_weyl_omega_obstruction_payload() -> dict:
    """Check whether the Janus determinant ratio uniquely fixes Omega."""

    checks = {
        "janus_determinant_ratio_available": True,
        "flrw_volume_ratio_formula_declared": True,
        "conformal_case_relation_declared": True,
        "determinant_ratio_fixes_volume_scale": True,
        "determinant_ratio_fixes_full_metric_conformal_factor": False,
        "near_pt_conformality_proved": False,
        "unique_omega_from_ratio_derived": False,
    }
    return {
        "status": "janus-determinant-ratio-to-weyl-omega-obstruction",
        "formulas": {
            "janus_ratio": "Q_det = sqrt(-g_minus / -g_plus)",
            "flrw_ratio": "Q_det = (N_minus * a_minus^3)/(N_plus * a_plus^3)",
            "if_conformal": "if g_minus = Xi^2 g_plus then Q_det = Xi^4",
        },
        "checks": checks,
        "what_is_closed": [
            "determinant ratio is a Janus-native volume coupling",
            "in a conformal special case it would give a fourth power of a conformal factor",
        ],
        "what_blocks": [
            "Janus does not currently prove g_minus is conformal to g_plus near PT",
            "a volume ratio does not determine lapse/scale/anistropy separately",
            "there is no unique Omega map without an extra conformality or gauge condition",
        ],
        "closed_now": all(checks.values()),
        "bottom_line": (
            "The determinant ratio is relevant but not enough. It can seed an Omega "
            "law only after a near-PT conformality theorem or gauge condition is derived."
        ),
    }


def weyl_cusp_late_sn_matching_boundary_conditions_payload() -> dict:
    """State the non-rustine boundary conditions needed to attach to late SN."""

    checks = {
        "late_sn_branch_preserved_condition_declared": True,
        "pt_cusp_condition_declared": True,
        "smooth_clock_condition_declared": True,
        "boundary_value_problem_formulated": True,
        "omega_differential_equation_available": True,
        "omega_boundary_solution_derived": False,
        "late_sn_matching_without_extra_law_proved": False,
    }
    return {
        "status": "janus-weyl-cusp-late-sn-matching-boundary-conditions",
        "boundary_conditions": {
            "pt_cusp": "Omega -> 0 with finite g_hat data",
            "late_sn_recovery": "Omega -> 1 and d ln(Omega)/d tau_hat -> 0 on the published late branch",
            "clock_smoothness": "H_plus finite wherever the late branch is regular",
        },
        "checks": checks,
        "boundary_problem_closed": all(
            checks[key]
            for key in [
                "late_sn_branch_preserved_condition_declared",
                "pt_cusp_condition_declared",
                "smooth_clock_condition_declared",
                "boundary_value_problem_formulated",
                "omega_differential_equation_available",
            ]
        ),
        "matching_solution_closed": (
            checks["omega_boundary_solution_derived"]
            and checks["late_sn_matching_without_extra_law_proved"]
        ),
        "bottom_line": (
            "The matching problem is now a precise boundary-value problem for Omega. "
            "It is not solved until the conformal trace equation is fed with active "
            "Janus sources and boundary data."
        ),
    }


def conformal_trace_source_content_audit_payload() -> dict:
    """Audit whether the trace equation sees the early plasma sources."""

    checks = {
        "trace_equation_available": True,
        "radiation_trace_zero": True,
        "photon_plasma_not_sourced_by_trace": True,
        "baryon_dust_trace_nonzero": True,
        "negative_sector_trace_possible": True,
        "full_pre_drag_source_closed_by_trace": False,
    }
    return {
        "status": "janus-conformal-trace-source-content-audit",
        "source_trace_table": [
            {"component": "photons/radiation", "trace": "0", "seen_by_trace_equation": False},
            {"component": "baryons/nonrelativistic matter", "trace": "approximately -rho_b", "seen_by_trace_equation": True},
            {"component": "negative-sector dust", "trace": "model-dependent signed trace", "seen_by_trace_equation": True},
            {"component": "cosmological constant/vacuum", "trace": "nonzero", "seen_by_trace_equation": True},
        ],
        "checks": checks,
        "trace_is_sufficient_for_predrag": False,
        "recommended_projection": "ConformalEinstein00",
        "bottom_line": (
            "The trace equation is real but not sufficient for pre-drag physics: "
            "the dominant photon/radiation component is trace-free. The next "
            "dynamical route must use the 00/Friedmann projection."
        ),
    }


def conformal_einstein_00_radiation_omega_route_payload() -> dict:
    """Use the 00/Friedmann projection so radiation can source Omega."""

    checks = {
        "gplus_weyl_kinematics_available": True,
        "friedmann_00_projection_declared": True,
        "radiation_source_visible_in_00": True,
        "baryon_source_visible_in_00": True,
        "negative_sector_effective_source_visible_in_00": True,
        "hat_H_input_derived": False,
        "rho_eff_plus_derived": False,
        "omega_boundary_condition_derived": False,
    }
    return {
        "status": "janus-conformal-einstein-00-radiation-omega-route",
        "equation": "(H_hat + d ln(Omega)/d tau_hat)^2 + k/a_hat^2 = Omega^2*kappa_eff*rho_eff_plus/3",
        "source_requirement": {
            "rho_eff_plus": "rho_r_plus + rho_b_plus + projected_negative_sector + possible vacuum/reference term",
            "radiation_scaling": "must be derived in g(+) Jordan frame, not imported as LCDM ruler",
        },
        "checks": checks,
        "projection_choice_closed": all(
            checks[key]
            for key in [
                "gplus_weyl_kinematics_available",
                "friedmann_00_projection_declared",
                "radiation_source_visible_in_00",
                "baryon_source_visible_in_00",
                "negative_sector_effective_source_visible_in_00",
            ]
        ),
        "omega_solution_closed": (
            checks["hat_H_input_derived"]
            and checks["rho_eff_plus_derived"]
            and checks["omega_boundary_condition_derived"]
        ),
        "bottom_line": (
            "The 00/Friedmann projection is the correct early-plasma route. It "
            "keeps radiation in the source, but still needs hat_H, rho_eff_plus, "
            "and Omega boundary data from Janus."
        ),
    }


def hat_background_candidate_matrix_payload() -> dict:
    """Rank possible conformal backgrounds for the Weyl cusp."""

    candidates = [
        {
            "name": "ProjectiveS4RP4ConformalBackground",
            "rank": 1,
            "janus_native": True,
            "route": "derive g_hat from the S4_L -> RP4_L projective conformal geometry",
            "blocker": "need explicit conformal time/curvature map near PT",
        },
        {
            "name": "FlatMilneReferenceBackground",
            "rank": 2,
            "janus_native": "reference-compatible",
            "route": "use flat/Milne as a zero-energy reference conformal frame",
            "blocker": "reference choice, not a Janus-derived background unless justified by PT limit",
        },
        {
            "name": "MinusSectorBackground",
            "rank": 3,
            "janus_native": True,
            "route": "use g(-) or a bimetric average as g_hat",
            "blocker": "requires near-PT relation between g(+) and g(-)",
        },
        {
            "name": "ArbitraryRegularHatMetric",
            "rank": 4,
            "janus_native": False,
            "route": "choose any regular conformal metric",
            "blocker": "too much gauge freedom; not predictive",
        },
    ]
    return {
        "status": "janus-hat-background-candidate-matrix",
        "candidates": candidates,
        "recommended_next": "ProjectiveS4RP4ConformalBackground",
        "fallback_reference": "FlatMilneReferenceBackground",
        "bottom_line": (
            "The best no-rustine hat background is the projective S4/RP4 conformal "
            "geometry. Flat/Milne is useful only as a reference check."
        ),
    }


def projective_s4_rp4_conformal_background_payload() -> dict:
    """Use the S4_L -> RP4_L topology to supply the conformal hat background."""

    checks = {
        "s4_l_cover_declared": True,
        "rp4_antipodal_quotient_declared": True,
        "stereographic_chart_declared": True,
        "flat_hat_metric_available_on_punctured_chart": True,
        "pt_point_as_conformal_infinity_declared": True,
        "omega_s4_conformal_factor_declared": True,
        "z2_projective_identification_declared": True,
        "absolute_L_fixed_by_geometry": False,
        "lorentzian_flrw_time_derived": False,
        "rho_eff_plus_derived": False,
    }
    return {
        "status": "janus-projective-s4-rp4-conformal-background",
        "geometry": {
            "cover": "S4_L",
            "quotient": "RP4_L = S4_L/(x ~ -x)",
            "chart": "S4_L minus one PT point is conformal to R4",
            "hat_metric": "flat chart metric on punctured conformal patch",
            "omega_s4": "Omega_S4(r) = 2 L^2/(L^2 + r^2)",
            "pt_limit": "r -> infinity gives Omega_S4 -> 0",
        },
        "checks": checks,
        "hat_background_geometry_closed": all(
            checks[key]
            for key in [
                "s4_l_cover_declared",
                "rp4_antipodal_quotient_declared",
                "stereographic_chart_declared",
                "flat_hat_metric_available_on_punctured_chart",
                "pt_point_as_conformal_infinity_declared",
                "omega_s4_conformal_factor_declared",
                "z2_projective_identification_declared",
            ]
        ),
        "predictive_cosmology_closed": (
            checks["absolute_L_fixed_by_geometry"]
            and checks["lorentzian_flrw_time_derived"]
            and checks["rho_eff_plus_derived"]
        ),
        "bottom_line": (
            "The S4/RP4 projective geometry can supply a natural conformal hat "
            "background and PT cusp map. It does not by itself fix L, Lorentzian "
            "time, or the effective cosmological source."
        ),
    }


def janus_bimetric_rho_eff_plus_source_contract_payload() -> dict:
    """Reduce published Janus coupled equations to a plus-sector effective source contract."""

    checks = {
        "m15_coupled_equations_available": True,
        "determinant_ratio_factor_available": True,
        "plus_sector_geodesic_clock_available": True,
        "signed_energy_conservation_available": True,
        "rho_eff_plus_formula_declared": True,
        "rho_plus_radiation_component_derived": False,
        "rho_plus_baryon_component_derived": False,
        "rho_minus_projection_component_derived": False,
        "pre_drag_scaling_derived": False,
    }
    return {
        "status": "janus-bimetric-rho-eff-plus-source-contract",
        "source_anchors": {
            "M15": "G(+) = chi [T(+) + sqrt(-g(-)/-g(+)) T(-)]",
            "X2022": "rho(+) c(+)^2 a(+)^3 + rho(-) c(-)^2 a(-)^3 = Cst",
        },
        "contract": {
            "Q_det": "sqrt(-g_minus / -g_plus)",
            "T_eff_plus": "T_plus + Q_det * T_minus",
            "rho_eff_plus_00": "rho_plus + Q_det * rho_minus_projected",
            "pre_drag_extension": "rho_plus = rho_r_plus + rho_b_plus + ...",
        },
        "checks": checks,
        "source_contract_closed": all(
            checks[key]
            for key in [
                "m15_coupled_equations_available",
                "determinant_ratio_factor_available",
                "plus_sector_geodesic_clock_available",
                "signed_energy_conservation_available",
                "rho_eff_plus_formula_declared",
            ]
        ),
        "active_predrag_source_closed": (
            checks["rho_plus_radiation_component_derived"]
            and checks["rho_plus_baryon_component_derived"]
            and checks["rho_minus_projection_component_derived"]
            and checks["pre_drag_scaling_derived"]
        ),
        "bottom_line": (
            "The plus-sector effective source contract is derivable from published "
            "Janus equations. The active pre-drag components are not: radiation, "
            "baryons, and minus-sector projection still need native scalings."
        ),
    }


def projective_hhat_from_s4rp4_limit_payload() -> dict:
    """Check whether S4/RP4 fixes H_hat or only the conformal class."""

    checks = {
        "conformal_hat_metric_available": True,
        "pt_cusp_coordinate_available": True,
        "omega_s4_factor_available": True,
        "hat_curvature_scale_depends_on_L": True,
        "absolute_L_fixed": False,
        "lorentzian_time_slicing_fixed": False,
        "hat_H_as_observable_clock_fixed": False,
    }
    return {
        "status": "janus-projective-hhat-from-s4rp4-limit",
        "closed_geometry": [
            "hat conformal class",
            "PT cusp coordinate",
            "Omega_S4(r)",
        ],
        "not_fixed_by_topology": [
            "absolute length L",
            "Lorentzian time slicing",
            "observable H_hat",
        ],
        "checks": checks,
        "hhat_geometry_closed": (
            checks["conformal_hat_metric_available"]
            and checks["pt_cusp_coordinate_available"]
            and checks["omega_s4_factor_available"]
        ),
        "hhat_dynamics_closed": (
            checks["absolute_L_fixed"]
            and checks["lorentzian_time_slicing_fixed"]
            and checks["hat_H_as_observable_clock_fixed"]
        ),
        "bottom_line": (
            "S4/RP4 fixes the conformal background geometry, not the physical "
            "H_hat. Topology gives the class; dynamics still needs L and a "
            "Lorentzian clock."
        ),
    }


def omega_00_solvability_frontier_payload() -> dict:
    """Combine H_hat and rho_eff_plus attempts into the final Omega frontier."""

    hhat = projective_hhat_from_s4rp4_limit_payload()
    rho = janus_bimetric_rho_eff_plus_source_contract_payload()
    projection = conformal_einstein_00_radiation_omega_route_payload()
    return {
        "status": "janus-omega-00-solvability-frontier",
        "equation": projection["equation"],
        "closed": {
            "gplus_weyl_kinematics": True,
            "projective_hat_conformal_geometry": hhat["hhat_geometry_closed"],
            "plus_sector_source_contract": rho["source_contract_closed"],
            "00_projection_choice": projection["projection_choice_closed"],
        },
        "still_open": {
            "absolute_L": not hhat["checks"]["absolute_L_fixed"],
            "lorentzian_time_slicing": not hhat["checks"]["lorentzian_time_slicing_fixed"],
            "observable_H_hat": not hhat["checks"]["hat_H_as_observable_clock_fixed"],
            "predrag_rho_plus_components": not rho["active_predrag_source_closed"],
            "omega_boundary_condition": not projection["checks"]["omega_boundary_condition_derived"],
        },
        "can_solve_omega_now": False,
        "is_same_old_blocker": (
            "same family: missing physical scale/source; cleaner form: no finite "
            "Sigma throat or arbitrary counterterm remains in the equation."
        ),
        "bottom_line": (
            "We reached the bottom of the non-throat Weyl-cusp branch. The equation "
            "is real and Janus-sourced at contract level, but a predictive solution "
            "requires L, Lorentzian time, pre-drag source scalings, and an Omega "
            "boundary condition."
        ),
    }


def active_normal_connection_primitives_availability_payload(
    root: Path | str = Path("."),
) -> dict:
    """Inspect whether current active Z2/Sigma files can supply omega_perp."""

    root = Path(root)
    active = root / "outputs" / "active_z2_sigma"
    manifest_path = active / "normal_connection_frame_primitives.json"
    unit_frame = _read_json_if_present(active / "sigma_unit_frame_inputs.json")
    coframe = _read_json_if_present(active / "coframe_connection_pullback_components_inputs.json")
    torsion = _read_json_if_present(active / "torsion_pullback_components_inputs.json")

    unit_frame_local_only = bool(unit_frame and unit_frame.get("full_embedding_claimed") is False)
    coframe_torsionless_baseline = bool(coframe and coframe.get("torsionless_baseline_only") is True)
    torsion_zero = bool(torsion and torsion.get("torsion_antisymmetry_residual_max_abs") == 0.0)
    return {
        "status": "janus-active-normal-connection-primitives-availability",
        "required_manifest": str(manifest_path),
        "required_manifest_present": manifest_path.exists(),
        "existing_inputs_checked": {
            "sigma_unit_frame_inputs.json": unit_frame is not None,
            "coframe_connection_pullback_components_inputs.json": coframe is not None,
            "torsion_pullback_components_inputs.json": torsion is not None,
        },
        "why_current_inputs_do_not_close": {
            "unit_frame_is_local_not_full_embedding": unit_frame_local_only,
            "coframe_is_torsionless_baseline": coframe_torsionless_baseline,
            "torsion_pullback_is_zero": torsion_zero,
            "missing_collar_u_dependence": True,
            "missing_partial_u_normal_frame": True,
            "missing_ambient_connection_u": True,
        },
        "can_materialize_active_omega_perp_now": False,
        "safe_to_create_zero_manifest_as_proof": False,
        "next_required": [
            "active collar embedding X(lambda,u)",
            "normal frame N_A(lambda,u)",
            "partial_u N_A(lambda,u)",
            "ambient connection Gamma_u(lambda,u)",
            "ambient metric g(lambda,u)",
        ],
        "bottom_line": (
            "The present Z2/Sigma assets are local and torsionless. They are useful "
            "for sign/projection audits, but they cannot produce the active normal "
            "connection needed for A_normal without a genuine collar embedding."
        ),
    }
