from __future__ import annotations

from pathlib import Path
import csv
import json
import math

try:
    from scripts.build_p0_eft_cmb_physical_visibility_transfer import (
        cl_proxy,
        integrate_transfer_with_physical_visibility,
    )
    from scripts.build_p0_eft_cmb_visibility_physical import build_payload as visibility_payload
    from scripts.build_p0_eft_cmb_weyl_transfer_integration import weyl_equation_source
    from scripts.build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_cmb_physical_visibility_transfer import cl_proxy, integrate_transfer_with_physical_visibility
    from build_p0_eft_cmb_visibility_physical import build_payload as visibility_payload
    from build_p0_eft_cmb_weyl_transfer_integration import weyl_equation_source
    from build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_minimal_boltzmann_hierarchy.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_minimal_boltzmann_hierarchy.json")
CSV_PATH = Path("outputs/reports/p0_eft_cmb_minimal_boltzmann_cl_proxy.csv")


def bounded_potential(k: float, z: float, constants: dict, radion: list[dict]) -> float:
    raw = weyl_equation_source(k, z, constants, radion)
    return math.tanh(raw / 1e6)


def integrate_minimal_hierarchy(k: float, constants: dict, radion: list[dict], visibility: dict) -> dict:
    z0 = 1400.0
    z1 = 700.0
    steps = 700
    dz = (z1 - z0) / steps
    theta0 = 1.0
    theta1 = 0.0
    delta_b = 1.0
    v_b = 0.0
    samples = []
    for i in range(steps + 1):
        z = z0 + dz * i
        vis = math.exp(-0.5 * ((z - visibility["z_star"]) / visibility["sigma_z"]) ** 2)
        psi = bounded_potential(k, z, constants, radion)
        samples.append((z, vis, theta0, psi))
        drag = 1.0 + 0.002 * abs(z - visibility["z_star"])
        dtheta0 = -k * theta1 + 0.02 * psi
        dtheta1 = k * (theta0 + psi) / 3.0 - drag * (theta1 - v_b)
        ddelta_b = -k * v_b
        dv_b = -0.5 * v_b + k * psi + drag * (theta1 - v_b)
        theta0 += dz * dtheta0 * -1e-3
        theta1 += dz * dtheta1 * -1e-3
        delta_b += dz * ddelta_b * -1e-3
        v_b += dz * dv_b * -1e-3
    norm = sum(row[1] for row in samples) or 1.0
    theta_transfer = sum(vis * (theta + psi) for _, vis, theta, psi in samples) / norm
    lensing_transfer = sum(vis * psi / (1.0 + z) for z, vis, _, psi in samples) / norm
    return {
        "k": k,
        "theta_transfer": theta_transfer,
        "weyl_lensing_transfer": lensing_transfer,
        "theta0_final": theta0,
        "theta1_final": theta1,
        "delta_b_final": delta_b,
        "v_b_final": v_b,
    }


def build_payload() -> dict:
    theta = theta_payload()
    visibility = visibility_payload()
    constants, radion = master_branch_background()
    ks = [10 ** (-3 + i * (3.0 / 30.0)) for i in range(31)]
    transfer_rows = [integrate_minimal_hierarchy(k, constants, radion, visibility) for k in ks]
    reference_rows = [integrate_transfer_with_physical_visibility(k, constants, radion, visibility) for k in ks]
    ells = [2, 10, 30, 100, 300, 800, 1200, 2000]
    cl_rows = [
        {"ell": ell, "cl_tt_proxy": cl_proxy(ell, transfer_rows, float(theta["theta_star_proxy_unit"]))}
        for ell in ells
    ]
    return {
        "description": "Minimal Janus-Holst photon-baryon Boltzmann hierarchy replacing the transfer proxy block.",
        "status": "cmb-minimal-boltzmann-hierarchy-integrated",
        "weyl_source_equation_used": True,
        "physical_visibility_used": True,
        "minimal_boltzmann_hierarchy_integrated": True,
        "full_boltzmann_hierarchy_validated": False,
        "cl_proxy_computed": True,
        "direct_cmb_likelihood_ready": False,
        "transfer_sample": [transfer_rows[0], transfer_rows[len(transfer_rows) // 2], transfer_rows[-1]],
        "reference_transfer_sample": [reference_rows[0], reference_rows[len(reference_rows) // 2], reference_rows[-1]],
        "cl_proxy": cl_rows,
        "next_required": "validate the hierarchy against a full photon-baryon-neutrino system and add a primordial spectrum/Planck likelihood.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Minimal Boltzmann Hierarchy",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Minimal hierarchy integrated: {payload['minimal_boltzmann_hierarchy_integrated']}",
        f"Full hierarchy validated: {payload['full_boltzmann_hierarchy_validated']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        "",
        "## C_ell Proxy",
        "",
        "| ell | C_ell TT proxy |",
        "|---:|---:|",
    ]
    for row in payload["cl_proxy"]:
        lines.append(f"| {row['ell']} | {row['cl_tt_proxy']:.6g} |")
    lines.extend(["", "## Next", "", payload["next_required"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, csv_path: Path = CSV_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(payload["cl_proxy"][0].keys()))
        writer.writeheader()
        writer.writerows(payload["cl_proxy"])
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
