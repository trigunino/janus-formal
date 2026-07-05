"""Partial active residual coefficient reductions for the Z2/Sigma counterterm."""

from __future__ import annotations

import numpy as np

from .z2_sigma_counterterm_tetrad_transport import _reject_forbidden


def _active(payload: dict, name: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{name} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{name} source must be active_derived")
    _reject_forbidden(payload)


def build_partial_counterterm_residual_coefficients(
    *,
    torsion_pullback_payload: dict,
    irreducible_torsion_payload: dict,
    holst_radial_payload: dict,
    immirzi_scalar_payload: dict | None = None,
) -> dict:
    """Reduce coefficients forced by the active torsionless Sigma branch.

    This does not invent the metric/extrinsic/Immirzi coefficients. It only
    records the coefficient reductions that follow from T|_Sigma=0 and
    E_HolstNiehYan=0 in the active payloads.
    """

    _active(torsion_pullback_payload, "torsion_pullback")
    _active(irreducible_torsion_payload, "irreducible_torsion")
    _active(holst_radial_payload, "holst_radial")
    if immirzi_scalar_payload is not None:
        _active(immirzi_scalar_payload, "immirzi_scalar")

    torsion = np.asarray(torsion_pullback_payload["torsion_T_internal_I_ab"], dtype=float)
    trace = np.asarray(irreducible_torsion_payload["trace_vector_values"], dtype=float)
    axial = np.asarray(
        irreducible_torsion_payload["axial_totally_antisymmetric_component_values"],
        dtype=float,
    )
    tensor = np.asarray(irreducible_torsion_payload["tensor_torsion_values"], dtype=float)
    holst = np.asarray(holst_radial_payload["term_values"], dtype=float)
    rchi_radial_ready = False
    rchi_radial_values = None
    if immirzi_scalar_payload is not None:
        rchi_radial_values = np.asarray(
            immirzi_scalar_payload["R_chi_partial_R_chi_values"],
            dtype=float,
        )
        rchi_radial_ready = bool(
            immirzi_scalar_payload.get("scalar_contraction_ready") is True
            and np.allclose(rchi_radial_values, 0.0, atol=1e-12)
        )

    torsionless = all(
        np.allclose(values, 0.0, atol=1e-12)
        for values in [torsion, trace, axial, tensor, holst]
    )
    r_t = np.zeros_like(torsion)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "coefficient_expansion_kind": "partial_active_torsionless_branch",
        "torsionless_sigma_branch": bool(torsionless),
        "R_T_A_values": r_t.tolist(),
        "R_T_A_ready": bool(torsionless),
        "R_T_A_provenance": (
            "active Sigma torsion pullback, irreducible torsion components, and "
            "Holst/Nieh-Yan radial term all vanish"
        ),
        "R_h_ab_ready": False,
        "R_K_ab_ready": False,
        "R_chi_ready": False,
        "R_chi_partial_R_chi_ready": rchi_radial_ready,
        "R_chi_partial_R_chi_values": None
        if rchi_radial_values is None
        else rchi_radial_values.tolist(),
        "R_chi_partial_R_chi_provenance": None
        if immirzi_scalar_payload is None
        else immirzi_scalar_payload.get("provenance"),
        "full_coefficient_expansion_explicit": False,
        "still_requires": ["R_h^{ab}", "R_K^{ab}", "R_chi"],
        "still_requires_for_radial_contractions": ["R_h^{ab} q_ab", "R_K^{ab} q_ab"]
        if rchi_radial_ready
        else ["R_h^{ab} q_ab", "R_K^{ab} q_ab", "R_chi partial_R chi"],
    }
