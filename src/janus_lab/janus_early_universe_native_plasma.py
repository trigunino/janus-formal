"""Native Janus early-universe plasma extension contract.

This module does not import a Lambda-CDM ruler. It records the calculable
microphysics consequences of the Janus 2026 variable-constants gauge and the
remaining active inputs needed to turn them into a BAO ruler.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class VariableConstantGauge:
    c_hat: float
    h_hat: float
    g_hat: float
    e_hat: float
    m_hat: float
    t_hat: float
    mu0_hat: float
    characteristic_length: float

    @classmethod
    def janus_2026_eq40(cls) -> "VariableConstantGauge":
        return cls(
            c_hat=-0.5,
            h_hat=1.5,
            g_hat=-1.0,
            e_hat=0.5,
            m_hat=1.0,
            t_hat=1.5,
            mu0_hat=1.0,
            characteristic_length=1.0,
        )

    def microphysics_scalings(self) -> dict[str, float | str]:
        """Return exponents versus the scale factor a.

        The derivations use only dimensional combinations fixed by the Eq. 40
        gauge:
        - alpha_fs ~ e^2/(h c)
        - lambda_C ~ h/(m c)
        - sigma_T ~ alpha_fs^2 lambda_C^2
        - E_rest ~ m c^2
        - E_ion ~ alpha_fs^2 m c^2
        """

        alpha_fs = 2.0 * self.e_hat - self.h_hat - self.c_hat
        compton_length = self.h_hat - self.m_hat - self.c_hat
        sigma_thomson_area = 2.0 * compton_length + 2.0 * alpha_fs
        rest_energy = self.m_hat + 2.0 * self.c_hat
        ionization_energy = rest_energy + 2.0 * alpha_fs
        metric_light_time = self.c_hat + self.t_hat - self.characteristic_length
        einstein_coupling_ratio = self.g_hat - 2.0 * self.c_hat
        return {
            "alpha_fs": alpha_fs,
            "compton_length": compton_length,
            "sigma_thomson_area": sigma_thomson_area,
            "rest_energy": rest_energy,
            "hydrogen_ionization_energy": ionization_energy,
            "metric_light_time_constraint": metric_light_time,
            "G_over_c2": einstein_coupling_ratio,
            "photon_temperature_law": "not fixed by Eq40 alone",
            "baryon_number_normalization": "not fixed by Eq40 alone",
            "pre_drag_H_J": "not fixed by Eq40 alone",
        }


@dataclass(frozen=True)
class NativePlasmaScalingCandidate:
    name: str
    photon_energy_exponent: float
    photon_number_density_exponent: float
    baryon_number_density_exponent: float
    baryon_rest_energy_exponent: float
    temperature_energy_exponent: float
    h_exponent: float
    sigma_thomson_exponent: float
    c_exponent: float
    h_j_exponent: float
    phase_space_occupation_exponent: float = 0.0

    @property
    def rho_gamma_exponent(self) -> float:
        return self.photon_energy_exponent + self.photon_number_density_exponent

    @property
    def rho_baryon_energy_exponent(self) -> float:
        return self.baryon_rest_energy_exponent + self.baryon_number_density_exponent

    @property
    def baryon_loading_exponent(self) -> float:
        return self.rho_baryon_energy_exponent - self.rho_gamma_exponent

    @property
    def gamma_drag_exponent_before_ionization(self) -> float:
        return (
            self.baryon_number_density_exponent
            + self.sigma_thomson_exponent
            + self.c_exponent
            - self.baryon_loading_exponent
        )

    @property
    def gamma_over_h_exponent_before_ionization(self) -> float:
        return self.gamma_drag_exponent_before_ionization - self.h_j_exponent

    @property
    def blackbody_photon_number_density_exponent(self) -> float:
        return self.phase_space_occupation_exponent + 3.0 * (
            self.temperature_energy_exponent - (self.h_exponent + self.c_exponent)
        )

    @property
    def blackbody_matches_conserved_photon_number(self) -> bool:
        return self.blackbody_photon_number_density_exponent == self.photon_number_density_exponent

    @property
    def saha_temperature_over_ionization_exponent(self) -> float:
        return self.temperature_energy_exponent

    def verdict(self) -> str:
        if not self.blackbody_matches_conserved_photon_number:
            return "requires_photon_entropy_or_phase_space_production_law"
        if self.saha_temperature_over_ionization_exponent == 0.0:
            return "drag_epoch_not_selected_without_extra_ionization_entropy_law"
        return "can_select_drag_epoch_if_temperature_law_is_derived"


def candidate_plasma_scaling_laws() -> list[NativePlasmaScalingCandidate]:
    gauge = VariableConstantGauge.janus_2026_eq40()
    scalings = gauge.microphysics_scalings()
    sigma_t = float(scalings["sigma_thomson_area"])
    rest_energy = float(scalings["rest_energy"])

    return [
        NativePlasmaScalingCandidate(
            name="eq40_comoving_photon_energy",
            photon_energy_exponent=gauge.h_hat - gauge.t_hat,
            photon_number_density_exponent=-3.0 * gauge.characteristic_length,
            baryon_number_density_exponent=-3.0 * gauge.characteristic_length,
            baryon_rest_energy_exponent=rest_energy,
            temperature_energy_exponent=gauge.h_hat - gauge.t_hat,
            h_exponent=gauge.h_hat,
            sigma_thomson_exponent=sigma_t,
            c_exponent=gauge.c_hat,
            h_j_exponent=-gauge.t_hat,
        ),
        NativePlasmaScalingCandidate(
            name="thermodynamic_cooling_photon_energy",
            photon_energy_exponent=-1.0,
            photon_number_density_exponent=-3.0 * gauge.characteristic_length,
            baryon_number_density_exponent=-3.0 * gauge.characteristic_length,
            baryon_rest_energy_exponent=rest_energy,
            temperature_energy_exponent=-1.0,
            h_exponent=gauge.h_hat,
            sigma_thomson_exponent=sigma_t,
            c_exponent=gauge.c_hat,
            h_j_exponent=-gauge.t_hat,
        ),
        NativePlasmaScalingCandidate(
            name="phase_space_compensated_thermal_cooling",
            photon_energy_exponent=-1.0,
            photon_number_density_exponent=-3.0 * gauge.characteristic_length,
            baryon_number_density_exponent=-3.0 * gauge.characteristic_length,
            baryon_rest_energy_exponent=rest_energy,
            temperature_energy_exponent=-1.0,
            h_exponent=gauge.h_hat,
            sigma_thomson_exponent=sigma_t,
            c_exponent=gauge.c_hat,
            h_j_exponent=-gauge.t_hat,
            phase_space_occupation_exponent=3.0,
        ),
    ]


def native_plasma_extension_contract() -> dict:
    gauge = VariableConstantGauge.janus_2026_eq40()
    scalings = gauge.microphysics_scalings()
    candidates = candidate_plasma_scaling_laws()
    return {
        "status": "janus-early-universe-native-plasma-extension-contract",
        "source_anchor": "X2026-variable-constants Eq. 40 plus Z2/Sigma projection branch",
        "closed_by_eq40": {
            "fine_structure_invariant": scalings["alpha_fs"] == 0.0,
            "rest_energy_invariant": scalings["rest_energy"] == 0.0,
            "ionization_energy_invariant": scalings["hydrogen_ionization_energy"] == 0.0,
            "thomson_area_scales_as_a2": scalings["sigma_thomson_area"] == 2.0,
            "compton_length_scales_as_a": scalings["compton_length"] == 1.0,
        },
        "scaling_exponents": scalings,
        "candidate_plasma_scaling_laws": [
            {
                "name": candidate.name,
                "rho_gamma_exponent": candidate.rho_gamma_exponent,
                "rho_baryon_energy_exponent": candidate.rho_baryon_energy_exponent,
                "baryon_loading_exponent": candidate.baryon_loading_exponent,
                "Gamma_drag_exponent_before_ionization": candidate.gamma_drag_exponent_before_ionization,
                "Gamma_drag_over_H_exponent_before_ionization": candidate.gamma_over_h_exponent_before_ionization,
                "temperature_energy_exponent": candidate.temperature_energy_exponent,
                "phase_space_occupation_exponent": candidate.phase_space_occupation_exponent,
                "blackbody_photon_number_density_exponent": candidate.blackbody_photon_number_density_exponent,
                "blackbody_matches_conserved_photon_number": candidate.blackbody_matches_conserved_photon_number,
                "verdict": candidate.verdict(),
            }
            for candidate in candidates
        ],
        "native_plasma_equations": [
            "n_b^J(a) = N_b^J / V_+^J(a)",
            "rho_b^J(a) follows from active baryon number, variable mass gauge, and visible volume",
            "rho_gamma^J(a) requires active photon temperature/occupation law",
            "c_s^J/c_J = [3(1 + 3 rho_b^J/(4 rho_gamma^J))]^-1/2",
            "Gamma_drag^J = n_e^J sigma_T^J c_J / R_bgamma^J",
            "z_d^J solves Gamma_drag^J(z_d) = H_J(z_d)",
            "r_d^J = integral_{z_d}^{z_max} c_s^J(z)/H_J(z) dz",
        ],
        "model_must_add_or_derive": [
            "active baryon number charge N_b^J or equivalent density normalization",
            "active photon temperature/occupation law in variable-constants regime",
            "native entropy/phase-space law if cooling is required to select recombination",
            "visible electron/ionization history n_e^J or a native recombination law",
            "pre-drag two-sector H_J(a) from bimetric equations",
            "redshift/scale-factor map valid beyond the late SN branch z_max",
        ],
        "interpretation": (
            "If closed, the visible BAO ruler is not imported from Lambda-CDM. "
            "It is produced by a Janus early plasma whose local microphysics is "
            "constrained by the variable-constants gauge, while its densities and "
            "expansion history are fixed by the Z2/Sigma bimetric projection."
        ),
    }
