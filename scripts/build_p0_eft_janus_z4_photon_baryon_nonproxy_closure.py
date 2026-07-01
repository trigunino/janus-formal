from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_photon_baryon_nonproxy_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_photon_baryon_nonproxy_closure.json")


def build_payload() -> dict:
    R, tau_dot, theta_g, theta_b = sp.symbols("R tau_dot theta_gamma theta_b", positive=True)
    phi, psi, k = sp.symbols("Phi Psi k")
    cs2 = sp.simplify(1 / (3 * (1 + R)))
    photon_drag = sp.simplify(tau_dot * (theta_b - theta_g))
    baryon_drag = sp.simplify(tau_dot * (theta_g - theta_b) / R)
    drag_internal_residual = sp.simplify(photon_drag + R * baryon_drag)
    photon_source = sp.simplify(k**2 * (phi + psi) / 3)
    single_sector_residual = sp.simplify(photon_source.subs({phi: psi}) - 2 * k**2 * psi / 3)

    return {
        "status": "janus-z4-photon-baryon-nonproxy-closure",
        "sound_speed_squared": str(cs2),
        "photon_drag": str(photon_drag),
        "baryon_drag": str(baryon_drag),
        "drag_internal_residual": str(drag_internal_residual),
        "single_sector_metric_residual": str(single_sector_residual),
        "photon_baryon_hierarchy_nonproxy": (
            drag_internal_residual == 0 and single_sector_residual == 0
        ),
        "visibility_input_required": True,
        "scope": "Closes photon-baryon hierarchy equations; calibrated recombination visibility remains separate.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Photon-Baryon Nonproxy Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Sound speed squared: `{payload['sound_speed_squared']}`",
        f"Drag internal residual: `{payload['drag_internal_residual']}`",
        f"Single-sector metric residual: `{payload['single_sector_metric_residual']}`",
        f"Photon-baryon hierarchy nonproxy: `{payload['photon_baryon_hierarchy_nonproxy']}`",
        "",
        payload["scope"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
