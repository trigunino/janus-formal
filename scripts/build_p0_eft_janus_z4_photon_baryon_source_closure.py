from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_photon_baryon_source_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_photon_baryon_source_closure.json")


def build_payload() -> dict:
    B, k, tau_dot, R = sp.symbols("B k tau_dot R", nonzero=True)
    psi_p, psi_m, phi_p, phi_m = sp.symbols("Psi_plus Psi_minus Phi_plus Phi_minus")
    theta_g, theta_b = sp.symbols("theta_gamma theta_b")

    psi_master = psi_p + B * psi_m
    phi_master = phi_p + B * phi_m
    photon_metric_source = k**2 * (sp.Rational(1, 4) * sp.Symbol("delta_gamma") + phi_master)
    baryon_metric_source = k**2 * psi_master
    photon_drag = tau_dot * (theta_b - theta_g)
    baryon_drag = tau_dot * (theta_g - theta_b) / R
    weighted_drag_residual = sp.simplify(photon_drag + R * baryon_drag)

    single_sector_photon_residual = sp.simplify(
        photon_metric_source.subs({B: 0, psi_m: 0, phi_m: 0}) -
        k**2 * (sp.Rational(1, 4) * sp.Symbol("delta_gamma") + phi_p)
    )
    single_sector_baryon_residual = sp.simplify(
        baryon_metric_source.subs({B: 0, psi_m: 0}) - k**2 * psi_p
    )

    ready = (
        weighted_drag_residual == 0
        and single_sector_photon_residual == 0
        and single_sector_baryon_residual == 0
    )
    return {
        "status": "janus-z4-photon-baryon-source-closure",
        "psi_master": str(psi_master),
        "phi_master": str(phi_master),
        "photon_metric_source": str(photon_metric_source),
        "baryon_metric_source": str(baryon_metric_source),
        "weighted_drag_residual": str(weighted_drag_residual),
        "single_sector_photon_residual": str(single_sector_photon_residual),
        "single_sector_baryon_residual": str(single_sector_baryon_residual),
        "photon_baryon_source_closure_ready": ready,
        "coefficients_from_full_z4_action": False,
        "photon_baryon_hierarchy_nonproxy": False,
        "next_required": (
            "Derive phi_master and psi_master coefficients from the full Z4 "
            "scalar action and propagate them into a real Boltzmann integrator."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Photon-Baryon Source Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Closure ready: `{payload['photon_baryon_source_closure_ready']}`",
        f"Photon-baryon hierarchy nonproxy: `{payload['photon_baryon_hierarchy_nonproxy']}`",
        "",
        "## Residuals",
        "",
        f"- weighted drag residual: `{payload['weighted_drag_residual']}`",
        f"- single-sector photon residual: `{payload['single_sector_photon_residual']}`",
        f"- single-sector baryon residual: `{payload['single_sector_baryon_residual']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
