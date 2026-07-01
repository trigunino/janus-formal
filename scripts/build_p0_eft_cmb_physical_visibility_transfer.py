from __future__ import annotations

from pathlib import Path
import csv
import json

try:
    from scripts.build_p0_eft_cmb_visibility_physical import (
        build_payload as visibility_payload,
        visibility_physical,
    )
    from scripts.build_p0_eft_cmb_weyl_transfer_integration import (
        cl_proxy,
        weyl_equation_source,
    )
    from scripts.build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import (
        master_branch_background,
        trapezoid_integral,
    )
except ModuleNotFoundError:
    from build_p0_eft_cmb_visibility_physical import build_payload as visibility_payload, visibility_physical
    from build_p0_eft_cmb_weyl_transfer_integration import cl_proxy, weyl_equation_source
    from build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background, trapezoid_integral


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_physical_visibility_transfer.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_physical_visibility_transfer.json")
CSV_PATH = Path("outputs/reports/p0_eft_cmb_physical_visibility_cl_proxy.csv")


def integrate_transfer_with_physical_visibility(k: float, constants: dict, radion: list[dict], visibility: dict) -> dict:
    zs = [700.0 + (1400.0 - 700.0) * i / 700 for i in range(701)]
    raw = [visibility_physical(z, visibility["z_star"], visibility["sigma_z"]) for z in zs]
    norm = trapezoid_integral(zs, raw)
    vis = [v / norm for v in raw]
    source = [v * weyl_equation_source(k, z, constants, radion) for z, v in zip(zs, vis)]
    lens_source = [s / (1.0 + z) for s, z in zip(source, zs)]
    theta = trapezoid_integral(zs, source)
    lens = trapezoid_integral(zs, lens_source)
    return {"k": k, "theta_transfer": theta, "weyl_lensing_transfer": lens}


def build_payload() -> dict:
    theta = theta_payload()
    visibility = visibility_payload()
    constants, radion = master_branch_background()
    ks = [10 ** (-3 + i * (3.0 / 30.0)) for i in range(31)]
    transfer_rows = [integrate_transfer_with_physical_visibility(k, constants, radion, visibility) for k in ks]
    ells = [2, 10, 30, 100, 300, 800, 1200, 2000]
    cl_rows = [
        {"ell": ell, "cl_tt_proxy": cl_proxy(ell, transfer_rows, float(theta["theta_star_proxy_unit"]))}
        for ell in ells
    ]
    return {
        "description": "CMB transfer with Janus-Holst Weyl equation and physicalized recombination visibility.",
        "status": "cmb-transfer-physical-visibility-integrated",
        "weyl_source_equation_used": True,
        "physical_visibility_used": True,
        "visibility_z_star": visibility["z_star"],
        "visibility_sigma_z": visibility["sigma_z"],
        "boltzmann_hierarchy_is_still_proxy": True,
        "cl_proxy_computed": True,
        "direct_cmb_likelihood_ready": False,
        "transfer_sample": [transfer_rows[0], transfer_rows[len(transfer_rows) // 2], transfer_rows[-1]],
        "cl_proxy": cl_rows,
        "next_required": "replace the remaining growth/temperature proxy with a real photon-baryon Boltzmann hierarchy.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Physical Visibility Transfer",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Weyl source equation used: {payload['weyl_source_equation_used']}",
        f"Physical visibility used: {payload['physical_visibility_used']}",
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
