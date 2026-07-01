from __future__ import annotations

from pathlib import Path
import csv
import json
import math

try:
    from scripts.build_p0_eft_direct_cmb_end_to_end_scaffold import (
        cl_proxy,
        visibility,
    )
    from scripts.build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import (
        e2_janus_holst,
        interpolate,
        master_branch_background,
        trapezoid_integral,
    )
except ModuleNotFoundError:
    from build_p0_eft_direct_cmb_end_to_end_scaffold import cl_proxy, visibility
    from build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from build_p0_eft_janus_holst_distance_ruler_map import (
        e2_janus_holst,
        interpolate,
        master_branch_background,
        trapezoid_integral,
    )


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_weyl_transfer_integration.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_weyl_transfer_integration.json")
CSV_PATH = Path("outputs/reports/p0_eft_cmb_weyl_transfer_cl_proxy.csv")


def mu_janus_holst(k: float, a: float, constants: dict, radion: list[dict]) -> float:
    e2 = e2_janus_holst(a, {**constants, "spin_coeff": 0.0}, radion)
    omega_t = interpolate(radion, a, "Omega_T")
    return 1.0 + (161.0 / 36.0) * omega_t * k * k / (k * k + 1.5 * e2)


def sigma_janus_holst(k: float, a: float, constants: dict, radion: list[dict]) -> float:
    eta_slip = 1.0
    return mu_janus_holst(k, a, constants, radion) * (1.0 + eta_slip) / 2.0


def weyl_equation_source(k: float, z: float, constants: dict, radion: list[dict]) -> float:
    a = 1.0 / (1.0 + z)
    omega_m = constants["Omega_m0"] * a**-3
    growth_proxy = a / (1.0 + 0.05 * z / (1.0 + z))
    return -0.75 * omega_m * sigma_janus_holst(k, a, constants, radion) * growth_proxy / max(k * k, 1e-8)


def integrate_weyl_transfer(k: float, constants: dict, radion: list[dict]) -> dict:
    zs = [1400.0 * i / 700 for i in range(701)]
    vis = [visibility(z) for z in zs]
    norm = trapezoid_integral(zs, vis)
    source = [v * weyl_equation_source(k, z, constants, radion) for z, v in zip(zs, vis)]
    lens_source = [s / (1.0 + z) for s, z in zip(source, zs)]
    theta = trapezoid_integral(zs, source) / norm
    lens = trapezoid_integral(zs, lens_source) / norm
    return {"k": k, "theta_transfer": theta, "weyl_lensing_transfer": lens}


def build_payload() -> dict:
    theta = theta_payload()
    constants, radion = master_branch_background()
    ks = [10 ** (-3 + i * (3.0 / 30.0)) for i in range(31)]
    transfer_rows = [integrate_weyl_transfer(k, constants, radion) for k in ks]
    ells = [2, 10, 30, 100, 300, 800, 1200, 2000]
    cl_rows = [
        {"ell": ell, "cl_tt_proxy": cl_proxy(ell, transfer_rows, float(theta["theta_star_proxy_unit"]))}
        for ell in ells
    ]
    return {
        "description": "CMB transfer integration using the Janus-Holst Weyl source equation instead of the old Weyl proxy kernel.",
        "status": "cmb-weyl-transfer-integrated-with-source-equation",
        "weyl_source_equation_used": True,
        "visibility_is_still_proxy": True,
        "boltzmann_hierarchy_is_still_proxy": True,
        "cl_proxy_computed": True,
        "direct_cmb_likelihood_ready": False,
        "transfer_sample": [transfer_rows[0], transfer_rows[len(transfer_rows) // 2], transfer_rows[-1]],
        "cl_proxy": cl_rows,
        "next_required": "replace proxy visibility and growth/temperature hierarchy with physical recombination and Boltzmann equations.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Weyl Transfer Integration",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Weyl source equation used: {payload['weyl_source_equation_used']}",
        f"Visibility still proxy: {payload['visibility_is_still_proxy']}",
        f"Boltzmann hierarchy still proxy: {payload['boltzmann_hierarchy_is_still_proxy']}",
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
