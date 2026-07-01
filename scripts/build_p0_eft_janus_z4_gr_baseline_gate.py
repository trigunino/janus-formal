from __future__ import annotations

from pathlib import Path
import json
import math
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import (
    assemble_spectra,
    optical_window,
    solve_photon_baryon_sources,
    visibility,
)
from scripts.build_p0_eft_janus_z4_shape_diagnostic import band_score


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_gr_baseline_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_gr_baseline_gate.json")


def _shape_summary(rows: list[dict[str, float]]) -> dict:
    ell = np.array([row["ell"] for row in rows], dtype=float)
    return {
        "lowTT": band_score(ell, np.array([row["cl_tt"] for row in rows]), "tt", 2, 29),
        "highl_TT_peak1": band_score(ell, np.array([row["cl_tt"] for row in rows]), "tt", 30, 450),
        "highl_TE": band_score(ell, np.array([row["cl_te"] for row in rows]), "te", 30, 1200),
        "highl_EE": band_score(ell, np.array([row["cl_ee"] for row in rows]), "ee", 30, 1200),
        "lensing": band_score(ell, np.array([row["cl_pp"] for row in rows]), "pp", 8, 400),
    }


def build_payload() -> dict:
    eta = np.linspace(1.0, 14000.0, 420)
    k_grid = np.logspace(-4, -0.35, 80)
    rows = assemble_spectra(ells=sorted(set(list(range(2, 202, 10)) + list(range(202, 1202, 20)) + [1200])))
    g = visibility(eta)
    e_tau = optical_window(eta)
    sources = solve_photon_baryon_sources(k_grid, eta)
    theta0, vb, psi, psi_dot, pol_quad, weyl = sources
    visibility_norm = float(np.trapezoid(g, eta))
    finite_sources = all(np.isfinite(arr).all() for arr in sources)
    finite_spectra = all(
        math.isfinite(float(row[field]))
        for row in rows
        for field in ("cl_tt", "cl_te", "cl_ee", "cl_pp")
    )
    positive_auto = all(row["cl_tt"] >= 0.0 and row["cl_ee"] >= 0.0 and row["cl_pp"] >= 0.0 for row in rows)
    eta_star = float(eta[np.argmax(g)])
    visibility_width = float(np.sqrt(np.trapezoid(np.square(eta - eta_star) * g, eta)))
    isw_energy = float(np.trapezoid(np.mean(np.square(psi_dot), axis=0) * e_tau, eta))
    sw_energy = float(np.trapezoid(np.mean(np.square(theta0 + psi), axis=0) * g, eta))
    lens_energy = float(np.trapezoid(np.mean(np.square(weyl), axis=0), eta))
    acoustic_energy = float(np.trapezoid(np.mean(np.square(theta0) + np.square(vb), axis=0) * g, eta))
    return {
        "status": "janus-z4-gr-baseline-gate",
        "z4_sector_enabled": False,
        "negative_sector_enabled": False,
        "torsion_enabled": False,
        "solver_numerics_modified": False,
        "planck_validation_claimed": False,
        "visibility_normalized": abs(visibility_norm - 1.0) < 1.0e-10,
        "visibility_norm": visibility_norm,
        "visibility_eta_star": eta_star,
        "visibility_width": visibility_width,
        "finite_sources": bool(finite_sources),
        "finite_spectra": bool(finite_spectra),
        "positive_auto_spectra": bool(positive_auto),
        "source_energy_proxies": {
            "SW": sw_energy,
            "ISW": isw_energy,
            "acoustic": acoustic_energy,
            "lensing_weyl": lens_energy,
        },
        "shape_proxy": _shape_summary(rows),
        "gr_baseline_gate_ready": bool(
            abs(visibility_norm - 1.0) < 1.0e-10 and finite_sources and finite_spectra and positive_auto
        ),
        "verdict": (
            "This is a native-solver GR-off/Z4-off baseline integrity gate. It is not a "
            "LambdaCDM/Planck validation; it only checks that the CMB pipeline has a finite "
            "single-sector baseline before Z4 physics is activated."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 GR Baseline Gate",
        "",
        f"Status: `{payload['status']}`",
        f"GR baseline gate ready: `{payload['gr_baseline_gate_ready']}`",
        f"Visibility norm: `{payload['visibility_norm']}`",
        f"Finite sources: `{payload['finite_sources']}`",
        f"Finite spectra: `{payload['finite_spectra']}`",
        f"Positive auto spectra: `{payload['positive_auto_spectra']}`",
        f"Planck validation claimed: `{payload['planck_validation_claimed']}`",
        "",
        "## Source energy proxies",
    ]
    for key, value in payload["source_energy_proxies"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", payload["verdict"], ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
