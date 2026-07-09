"""Search candidates for the Janus photon phase-space occupation law.

The early-plasma extension found a precise target: a thermal cooling branch
needs an occupation/phase-space multiplier scaling as a^3. This module tests
candidate mechanisms against that exponent without treating them as proven.
"""

from __future__ import annotations

from dataclasses import dataclass
import math


REQUIRED_OCCUPATION_EXPONENT = 3.0


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
