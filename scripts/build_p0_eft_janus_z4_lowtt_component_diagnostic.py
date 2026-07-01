from __future__ import annotations

from pathlib import Path
import json
import math
import sys

import numpy as np
from scipy.special import spherical_jn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import (
    optical_window,
    primordial_power,
    solve_photon_baryon_sources,
    visibility,
)
from scripts.build_p0_eft_janus_z4_shape_diagnostic import band_score


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_lowtt_component_diagnostic.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_lowtt_component_diagnostic.json")


def _component_transfers(ell: int, k_grid: np.ndarray, eta: np.ndarray, sources: tuple) -> dict[str, np.ndarray]:
    eta0 = 14000.0
    g = visibility(eta)
    e_tau = optical_window(eta)
    x = np.outer(k_grid, eta0 - eta)
    j = spherical_jn(ell, x)
    jp = spherical_jn(ell, x, derivative=True)
    theta0, vb, psi, psi_dot, _pol_quad, _weyl = sources
    sw = np.trapezoid(g[None, :] * (theta0 + psi) * j, eta, axis=1)
    doppler = np.trapezoid(g[None, :] * vb * jp, eta, axis=1)
    isw = np.trapezoid(e_tau[None, :] * 2.0 * psi_dot * j, eta, axis=1)
    total = sw + doppler + isw
    return {"sw": sw, "doppler": doppler, "isw": isw, "total": total}


def _cl(pk: np.ndarray, k_grid: np.ndarray, transfer: np.ndarray) -> float:
    return float(4.0 * math.pi * np.trapezoid(pk * transfer * transfer, np.log(k_grid)))


def build_payload() -> dict:
    ells = np.arange(2, 30, dtype=float)
    k_grid = np.logspace(-4, -0.35, 150)
    eta = np.linspace(1.0, 14000.0, 420)
    pk = primordial_power(k_grid)
    sources = solve_photon_baryon_sources(k_grid, eta)
    rows = []
    for ell_float in ells:
        ell = int(ell_float)
        transfers = _component_transfers(ell, k_grid, eta, sources)
        sw = _cl(pk, k_grid, transfers["sw"])
        doppler = _cl(pk, k_grid, transfers["doppler"])
        isw = _cl(pk, k_grid, transfers["isw"])
        total = _cl(pk, k_grid, transfers["total"])
        component_sum = sw + doppler + isw
        rows.append(
            {
                "ell": ell,
                "cl_tt_total": total,
                "cl_tt_sw": sw,
                "cl_tt_doppler": doppler,
                "cl_tt_isw": isw,
                "component_sum_auto": component_sum,
                "interference_fraction": float((total - component_sum) / total) if total > 0.0 else 0.0,
                "sw_fraction_auto": float(sw / component_sum) if component_sum > 0.0 else 0.0,
                "doppler_fraction_auto": float(doppler / component_sum) if component_sum > 0.0 else 0.0,
                "isw_fraction_auto": float(isw / component_sum) if component_sum > 0.0 else 0.0,
            }
        )

    ell = np.array([row["ell"] for row in rows], dtype=float)
    total = np.array([row["cl_tt_total"] for row in rows], dtype=float)
    proxy = band_score(ell, total, "tt", 2, 29)
    mean_fractions = {
        "sw": float(np.mean([row["sw_fraction_auto"] for row in rows])),
        "doppler": float(np.mean([row["doppler_fraction_auto"] for row in rows])),
        "isw": float(np.mean([row["isw_fraction_auto"] for row in rows])),
        "interference": float(np.mean([row["interference_fraction"] for row in rows])),
    }
    dominant = max(("sw", "doppler", "isw"), key=lambda key: mean_fractions[key])
    return {
        "status": "janus-z4-lowtt-component-diagnostic",
        "native_z4_solver_used": True,
        "compressed_lcdm_parameters_used": False,
        "official_planck_likelihood_executed": False,
        "official_lowl_tt_rejected_elsewhere": True,
        "rows": rows,
        "lowtt_shape_proxy": proxy,
        "mean_component_fractions": mean_fractions,
        "dominant_lowtt_source": dominant,
        "lowtt_component_diagnostic_ready": True,
        "verdict": (
            "Low-l TT is decomposed into SW, Doppler and ISW auto-components. "
            "This diagnostic explains source dominance but is not an official low-l likelihood."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    frac = payload["mean_component_fractions"]
    lines = [
        "# Janus Z4 low-l TT Component Diagnostic",
        "",
        f"Status: `{payload['status']}`",
        f"Dominant low-l TT source: `{payload['dominant_lowtt_source']}`",
        f"Mean SW fraction: `{frac['sw']:.6g}`",
        f"Mean Doppler fraction: `{frac['doppler']:.6g}`",
        f"Mean ISW fraction: `{frac['isw']:.6g}`",
        f"Mean interference fraction: `{frac['interference']:.6g}`",
        f"Shape proxy chi2/dof: `{payload['lowtt_shape_proxy']['chi2_per_dof']:.6g}`",
        "",
        payload["verdict"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
