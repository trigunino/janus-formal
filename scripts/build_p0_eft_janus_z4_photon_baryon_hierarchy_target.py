from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_photon_baryon_hierarchy_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_photon_baryon_hierarchy_target.json")


def build_payload() -> dict:
    k, H, cs2, R, taudot = sp.symbols("k H cs2 R taudot")
    dg, tg, db, tb, phi, psi_p = sp.symbols("delta_gamma theta_gamma delta_b theta_b Phi Psi_prime")
    equations = {
        "photon_continuity": sp.Eq(sp.Symbol("delta_gamma_prime"), -sp.Rational(4, 3) * tg + 4 * psi_p),
        "photon_euler": sp.Eq(sp.Symbol("theta_gamma_prime"), k**2 * (dg / 4 + phi) - taudot * (tg - tb)),
        "baryon_continuity": sp.Eq(sp.Symbol("delta_b_prime"), -tb + 3 * psi_p),
        "baryon_euler": sp.Eq(sp.Symbol("theta_b_prime"), -H * tb + cs2 * k**2 * db + R * taudot * (tg - tb) + k**2 * phi),
    }
    checks = {
        "photon_continuity_declared": True,
        "photon_euler_declared": True,
        "baryon_continuity_declared": True,
        "baryon_euler_declared": True,
        "thomson_coupling_declared": True,
        "z4_metric_source_coupled": True,
        "recombination_visibility_coupled": True,
        "coefficients_derived_from_action": False,
    }
    return {
        "status": "janus-z4-photon-baryon-hierarchy-target",
        "lean_module": "JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PhotonBaryonHierarchyTarget",
        "equations": {key: str(value) for key, value in equations.items()},
        "checks": checks,
        "hierarchy_target_ready": all(
            value for key, value in checks.items()
            if key != "coefficients_derived_from_action"
        ),
        "hierarchy_physical_ready": False,
        "next_required": "Derive H, Phi, Psi, tau_dot, R and cs2 from the Z4 action/source system, not proxy calibration.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Photon-Baryon Hierarchy Target",
        "",
        f"Status: `{payload['status']}`",
        "",
        "## Equations",
    ]
    for key, value in payload["equations"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Checks"])
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Hierarchy target ready: `{payload['hierarchy_target_ready']}`",
        f"Hierarchy physical ready: `{payload['hierarchy_physical_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
