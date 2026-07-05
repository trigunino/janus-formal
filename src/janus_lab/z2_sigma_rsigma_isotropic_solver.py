"""Isotropic active Z2/Sigma R_Sigma balance solver."""

from __future__ import annotations

import numpy as np

from .z2_sigma_rsigma_equation import (
    assemble_rsigma_residual_payload,
    build_rsigma_certificate_from_residual_payload,
)


def solve_isotropic_rsigma_balance(
    *,
    a_grid,
    E_HolstNiehYan,
    E_matterFlux,
    E_counterterm,
    unit_intrinsic_metric_q_ab,
    kappa_Z2Sigma: float,
    z2_orientation_sign: float,
    certificate_payload: dict,
    term_provenance: dict,
) -> tuple[dict, dict]:
    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    q = np.asarray(unit_intrinsic_metric_q_ab, dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1]:
        raise ValueError("unit_intrinsic_metric_q_ab must be square")
    if not np.allclose(q, q.T):
        raise ValueError("unit_intrinsic_metric_q_ab must be symmetric")
    det_q = float(np.linalg.det(q))
    if det_q == 0.0 or not np.isfinite(det_q):
        raise ValueError("unit_intrinsic_metric_q_ab must be nondegenerate")
    if kappa_Z2Sigma <= 0.0:
        raise ValueError("kappa_Z2Sigma must be positive")
    if z2_orientation_sign not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +1.0 or -1.0")
    d = q.shape[0]
    if d <= 2:
        raise ValueError("isotropic Cartan-GHY balance solves R_Sigma only for intrinsic_dim > 2")

    shape = grid.shape
    holst = np.asarray(E_HolstNiehYan, dtype=float)
    matter = np.asarray(E_matterFlux, dtype=float)
    counter = np.asarray(E_counterterm, dtype=float)
    for name, values in [
        ("E_HolstNiehYan", holst),
        ("E_matterFlux", matter),
        ("E_counterterm", counter),
    ]:
        if values.shape != shape or not np.all(np.isfinite(values)):
            raise ValueError(f"{name} must be finite and aligned with a_grid")

    coeff = float(z2_orientation_sign) * np.sqrt(abs(det_q)) * d * (d - 1) / float(kappa_Z2Sigma)
    noncartan = holst + matter + counter
    target = -noncartan / coeff
    if np.any(target <= 0.0) or not np.all(np.isfinite(target)):
        raise ValueError("isotropic balance does not yield positive R_Sigma")
    radius = target ** (1.0 / float(d - 2))
    cartan = coeff * radius ** (d - 2)
    residual_payload = assemble_rsigma_residual_payload(
        a_grid=grid,
        E_CartanGHY=cartan,
        E_HolstNiehYan=holst,
        E_matterFlux=matter,
        E_counterterm=counter,
        term_provenance={
            "E_CartanGHY": term_provenance["E_CartanGHY"],
            "E_HolstNiehYan": term_provenance["E_HolstNiehYan"],
            "E_matterFlux": term_provenance["E_matterFlux"],
            "E_counterterm": term_provenance["E_counterterm"],
        },
    )
    cert_payload = dict(certificate_payload)
    cert_payload["a_grid"] = grid.tolist()
    cert_payload["R_Sigma_of_a"] = radius.tolist()
    cert_payload["z2_orientation_sign"] = float(z2_orientation_sign)
    cert_payload["R_Sigma_solution_certificate_type"] = "active_no_fit_solution"
    cert_payload["rsigma_payload_is_template"] = False
    cert_payload["rsigma_payload_not_solution_certificate"] = False
    cert_payload["R_Sigma_of_a_placeholder"] = False
    certificate = build_rsigma_certificate_from_residual_payload(
        residual_payload=residual_payload,
        certificate_payload=cert_payload,
    )
    cartan_term = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "term_name": "E_CartanGHY",
        "a_grid": grid.tolist(),
        "term_values": cartan.tolist(),
        "term_provenance": term_provenance["E_CartanGHY"],
        "isotropic_balance_coefficient": coeff,
    }
    return certificate, cartan_term
