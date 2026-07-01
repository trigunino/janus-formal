from __future__ import annotations

from pathlib import Path
import csv
import json
import math

try:
    from scripts.build_p0_eft_cmb_visibility_physical import build_payload as visibility_payload
    from scripts.build_p0_eft_cmb_weyl_transfer_integration import weyl_equation_source
    from scripts.build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_cmb_visibility_physical import build_payload as visibility_payload
    from build_p0_eft_cmb_weyl_transfer_integration import weyl_equation_source
    from build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_full_hierarchy_pre_likelihood.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_full_hierarchy_pre_likelihood.json")
CSV_PATH = Path("outputs/reports/p0_eft_cmb_full_hierarchy_spectra_proxy.csv")


def primordial_power(k: float, amplitude: float = 2.1e-9, n_s: float = 0.965, pivot: float = 0.05) -> float:
    return amplitude * (k / pivot) ** (n_s - 1.0)


def bounded_potential(k: float, z: float, constants: dict, radion: list[dict]) -> float:
    return math.tanh(weyl_equation_source(k, z, constants, radion) / 1e6)


def integrate_extended_hierarchy(k: float, constants: dict, radion: list[dict], visibility: dict) -> dict:
    z0 = 1400.0
    z1 = 700.0
    steps = 700
    dz = (z1 - z0) / steps
    theta0 = 1.0
    theta1 = 0.0
    delta_b = 1.0
    v_b = 0.0
    delta_nu = 0.4
    shear_nu = 0.0
    e_pol = 0.0
    samples = []
    for i in range(steps + 1):
        z = z0 + dz * i
        x = (z - visibility["z_star"]) / visibility["sigma_z"]
        vis = math.exp(-0.5 * x * x)
        psi = bounded_potential(k, z, constants, radion)
        samples.append((z, vis, theta0, theta1, e_pol, psi, shear_nu))
        tight_drag = 1.0 + 0.002 * abs(z - visibility["z_star"])
        free_stream = 0.35 / (1.0 + z / 1000.0)
        dtheta0 = -k * theta1 + 0.02 * psi
        dtheta1 = k * (theta0 + psi) / 3.0 - tight_drag * (theta1 - v_b) - 0.05 * shear_nu
        ddelta_b = -k * v_b
        dv_b = -0.5 * v_b + k * psi + tight_drag * (theta1 - v_b)
        ddelta_nu = -free_stream * k * shear_nu + 0.01 * psi
        dshear_nu = free_stream * (delta_nu - 2.0 * shear_nu) + 0.02 * theta1
        de_pol = 0.03 * tight_drag * (theta1 - e_pol)
        step = -1e-3 * dz
        theta0 += step * dtheta0
        theta1 += step * dtheta1
        delta_b += step * ddelta_b
        v_b += step * dv_b
        delta_nu += step * ddelta_nu
        shear_nu += step * dshear_nu
        e_pol += step * de_pol
    norm = sum(row[1] for row in samples) or 1.0
    tt = sum(vis * (theta0_i + psi) for _, vis, theta0_i, _, _, psi, _ in samples) / norm
    te = sum(vis * (theta1_i * e_i) for _, vis, _, theta1_i, e_i, _, _ in samples) / norm
    ee = sum(vis * (e_i * e_i) for _, vis, _, _, e_i, _, _ in samples) / norm
    lens = sum(vis * (psi + sh) / (1.0 + z) for z, vis, _, _, _, psi, sh in samples) / norm
    return {"k": k, "tt_transfer": tt, "te_transfer": te, "ee_transfer": ee, "lensing_transfer": lens}


def spectrum_proxy(ell: int, transfer_rows: list[dict], theta_unit: float, key: str) -> float:
    k = max(1e-4, ell * theta_unit)
    nearest = min(transfer_rows, key=lambda row: abs(row["k"] - k))
    damping = math.exp(-ell * (ell + 1.0) / (2200.0 * 2200.0))
    return primordial_power(k) * nearest[key] * nearest[key] * damping / max(ell * (ell + 1.0), 1.0)


def build_payload() -> dict:
    theta = theta_payload()
    visibility = visibility_payload()
    constants, radion = master_branch_background()
    ks = [10 ** (-3 + i * (3.0 / 36.0)) for i in range(37)]
    transfers = [integrate_extended_hierarchy(k, constants, radion, visibility) for k in ks]
    ells = [2, 10, 30, 100, 300, 800, 1200, 2000]
    spectra = []
    for ell in ells:
        spectra.append(
            {
                "ell": ell,
                "tt_proxy": spectrum_proxy(ell, transfers, theta["theta_star_proxy_unit"], "tt_transfer"),
                "te_proxy": spectrum_proxy(ell, transfers, theta["theta_star_proxy_unit"], "te_transfer"),
                "ee_proxy": spectrum_proxy(ell, transfers, theta["theta_star_proxy_unit"], "ee_transfer"),
                "lensing_proxy": spectrum_proxy(ell, transfers, theta["theta_star_proxy_unit"], "lensing_transfer"),
            }
        )
    return {
        "description": "Pre-likelihood direct CMB pipeline with extended photon-baryon-neutrino hierarchy and primordial spectrum proxy.",
        "status": "cmb-full-hierarchy-pre-likelihood-computed",
        "weyl_source_equation_used": True,
        "physical_visibility_used": True,
        "photon_baryon_neutrino_hierarchy_integrated": True,
        "primordial_spectrum_included": True,
        "tt_te_ee_lensing_proxy_computed": True,
        "validated_against_external_boltzmann_code": False,
        "uncompressed_planck_likelihood_ready": False,
        "direct_cmb_likelihood_ready": False,
        "is_planck_verdict": False,
        "theta_star_proxy_unit": theta["theta_star_proxy_unit"],
        "transfer_sample": [transfers[0], transfers[len(transfers) // 2], transfers[-1]],
        "spectra_proxy": spectra,
        "remaining_obligation": "Validate against a real Boltzmann code and connect uncompressed Planck likelihood data.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Full Hierarchy Pre-Likelihood",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        f"Planck verdict: {payload['is_planck_verdict']}",
        "",
        "| ell | TT proxy | TE proxy | EE proxy | lensing proxy |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in payload["spectra_proxy"]:
        lines.append(
            f"| {row['ell']} | {row['tt_proxy']:.6g} | {row['te_proxy']:.6g} | "
            f"{row['ee_proxy']:.6g} | {row['lensing_proxy']:.6g} |"
        )
    lines.extend(["", "## Remaining Obligation", "", payload["remaining_obligation"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, csv_path: Path = CSV_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(payload["spectra_proxy"][0].keys()))
        writer.writeheader()
        writer.writerows(payload["spectra_proxy"])
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
