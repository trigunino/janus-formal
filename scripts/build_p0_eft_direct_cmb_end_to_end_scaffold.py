from __future__ import annotations

from pathlib import Path
import csv
import json
import math

try:
    from scripts.build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from scripts.build_p0_eft_direct_cmb_transfer_scaffold import build_payload as transfer_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import (
        e2_janus_holst,
        interpolate,
        master_branch_background,
        trapezoid_integral,
    )
except ModuleNotFoundError:
    from build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from build_p0_eft_direct_cmb_transfer_scaffold import build_payload as transfer_payload
    from build_p0_eft_janus_holst_distance_ruler_map import (
        e2_janus_holst,
        interpolate,
        master_branch_background,
        trapezoid_integral,
    )


REPORT_PATH = Path("outputs/reports/p0_eft_direct_cmb_end_to_end_scaffold.md")
JSON_PATH = Path("outputs/reports/p0_eft_direct_cmb_end_to_end_scaffold.json")
CSV_PATH = Path("outputs/reports/p0_eft_direct_cmb_end_to_end_cl_proxy.csv")


def visibility(z: float, z_star: float = 1089.0, sigma_z: float = 85.0) -> float:
    return math.exp(-0.5 * ((z - z_star) / sigma_z) ** 2)


def weyl_source(k: float, z: float, constants: dict, radion: list[dict]) -> float:
    a = 1.0 / (1.0 + z)
    e2 = e2_janus_holst(a, {**constants, "spin_coeff": 0.0}, radion)
    omega_t = interpolate(radion, a, "Omega_T")
    mu = 1.0 + (161.0 / 36.0) * omega_t * k * k / (k * k + 1.5 * e2)
    decay = 1.0 / (1.0 + 0.15 * z / (1.0 + z))
    return mu * decay


def integrate_transfer(k: float, constants: dict, radion: list[dict]) -> dict:
    zs = [1400.0 * i / 700 for i in range(701)]
    vis = [visibility(z) for z in zs]
    norm = trapezoid_integral(zs, vis)
    theta_kernel = [v * weyl_source(k, z, constants, radion) for z, v in zip(zs, vis)]
    lens_kernel = [v * weyl_source(k, z, constants, radion) / (1.0 + z) for z, v in zip(zs, vis)]
    theta = trapezoid_integral(zs, theta_kernel) / norm
    lens = trapezoid_integral(zs, lens_kernel) / norm
    return {"k": k, "theta_transfer": theta, "weyl_lensing_transfer": lens}


def cl_proxy(ell: int, transfer_rows: list[dict], theta_unit: float) -> float:
    k = max(1e-4, ell * theta_unit)
    nearest = min(transfer_rows, key=lambda row: abs(row["k"] - k))
    damping = math.exp(-ell * (ell + 1.0) / (1800.0 * 1800.0))
    return nearest["theta_transfer"] ** 2 * damping / (ell * (ell + 1.0))


def build_payload() -> dict:
    theta = theta_payload()
    transfer = transfer_payload()
    constants, radion = master_branch_background()
    ks = [10 ** (-3 + i * (3.0 / 30.0)) for i in range(31)]
    transfer_rows = [integrate_transfer(k, constants, radion) for k in ks]
    ells = [2, 10, 30, 100, 300, 800, 1200, 2000]
    cl_rows = [
        {
            "ell": ell,
            "cl_tt_proxy": cl_proxy(ell, transfer_rows, float(theta["theta_star_proxy_unit"])),
        }
        for ell in ells
    ]
    return {
        "description": "End-to-end direct CMB scaffold: Weyl source, visibility kernel, transfer proxy, and C_ell proxy.",
        "status": "direct-cmb-end-to-end-proxy-computed-not-planck-likelihood",
        "uses_lcdm_compressed_planck_parameters_as_verdict": False,
        "theta_star_proxy_ready": theta["janus_distance_ruler_proxy_ready"],
        "transfer_scaffold_ready": transfer["transfer_equations_encoded"],
        "weyl_source_proxy_ready": True,
        "visibility_proxy_ready": True,
        "boltzmann_proxy_integrated": True,
        "cl_proxy_computed": True,
        "direct_cmb_likelihood_ready": False,
        "is_planck_verdict": False,
        "theta_star_proxy_unit": theta["theta_star_proxy_unit"],
        "transfer_sample": [transfer_rows[0], transfer_rows[len(transfer_rows) // 2], transfer_rows[-1]],
        "cl_proxy": cl_rows,
        "remaining_obligation": (
            "Replace proxy kernels with a validated Janus-Holst Boltzmann hierarchy, "
            "recombination visibility, primordial spectrum, and Planck uncompressed likelihood."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Direct CMB End-to-End Scaffold",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Planck verdict: {payload['is_planck_verdict']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        "",
        "## Flags",
        "",
    ]
    for key in [
        "theta_star_proxy_ready",
        "transfer_scaffold_ready",
        "weyl_source_proxy_ready",
        "visibility_proxy_ready",
        "boltzmann_proxy_integrated",
        "cl_proxy_computed",
    ]:
        lines.append(f"- {key}: {payload[key]}")
    lines.extend(["", "## C_ell Proxy", "", "| ell | C_ell TT proxy |", "|---:|---:|"])
    for row in payload["cl_proxy"]:
        lines.append(f"| {row['ell']} | {row['cl_tt_proxy']:.6g} |")
    lines.extend(["", "## Remaining Obligation", "", payload["remaining_obligation"], ""])
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
