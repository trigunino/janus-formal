from __future__ import annotations

from pathlib import Path
import csv
import json
import math

try:
    from scripts.build_p0_eft_growth_no_fit_numerical_export import branch_constants, integrate_radion
    from scripts.run_p0_eft_spinor_torsion_scan import solve_omega_m0_with_spin
except ModuleNotFoundError:
    from build_p0_eft_growth_no_fit_numerical_export import branch_constants, integrate_radion
    from run_p0_eft_spinor_torsion_scan import solve_omega_m0_with_spin


REPORT_PATH = Path("outputs/reports/p0_eft_janus_holst_distance_ruler_map.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_holst_distance_ruler_map.json")
CSV_PATH = Path("outputs/reports/p0_eft_janus_holst_distance_ruler_map.csv")


def trapezoid_integral(xs: list[float], ys: list[float]) -> float:
    return sum((x1 - x0) * (y0 + y1) / 2.0 for x0, x1, y0, y1 in zip(xs, xs[1:], ys, ys[1:]))


def interpolate(rows: list[dict], a: float, key: str) -> float:
    ordered = sorted(rows, key=lambda row: row["a"])
    if a <= ordered[0]["a"]:
        return float(ordered[0][key])
    if a >= ordered[-1]["a"]:
        return float(ordered[-1][key])
    for left, right in zip(ordered, ordered[1:]):
        if left["a"] <= a <= right["a"]:
            t = (a - left["a"]) / (right["a"] - left["a"])
            return float(left[key]) + t * (float(right[key]) - float(left[key]))
    return float(ordered[-1][key])


def master_branch_background(z_max: float = 2.5) -> tuple[dict, list[dict]]:
    _ = z_max
    mpl2 = 64.0
    eps = -1.0
    h2 = 0.5
    omega_ds = 0.4
    spin_coeff = 2.0
    eta_holst = -2.0
    z_sigma = 0.5
    a_sigma = 1.0 / (1.0 + z_sigma)
    constants = branch_constants(
        mpl2=mpl2,
        eps=eps,
        h2=h2,
        rho_ds=omega_ds * 3.0 * mpl2 * h2,
    )
    radion = integrate_radion(constants, a_sigma=a_sigma)
    omega_t0 = radion[-1]["Omega_T"]
    omega_m0 = solve_omega_m0_with_spin(omega_ds, omega_t0, spin_coeff)
    if omega_m0 is None:
        raise ValueError("no positive matter root")
    return {
        **constants,
        "eta_holst": eta_holst,
        "z_sigma": z_sigma,
        "a_sigma": a_sigma,
        "Omega_dS_residual": omega_ds,
        "Omega_m0": omega_m0,
        "Omega_T0": omega_t0,
        "spin_coeff": spin_coeff,
    }, radion


def e2_janus_holst(a: float, constants: dict, radion: list[dict]) -> float:
    omega_m = constants["Omega_m0"] * a ** -3
    omega_t = constants.get("Omega_T_constant_override", interpolate(radion, a, "Omega_T"))
    return constants["Omega_dS_residual"] + omega_m + omega_t + constants["spin_coeff"] * omega_m * omega_m


def distance_row(z: float, constants: dict, radion: list[dict], samples: int = 512) -> dict:
    if z == 0.0:
        e = math.sqrt(e2_janus_holst(1.0, constants, radion))
        return {"z": z, "E": e, "D_H_unit": 1.0 / e, "D_M_unit": 0.0, "D_V_unit": 0.0}
    zs = [z * i / (samples - 1) for i in range(samples)]
    inv_e = []
    for value in zs:
        a = 1.0 / (1.0 + value)
        inv_e.append(1.0 / math.sqrt(e2_janus_holst(a, constants, radion)))
    d_m = trapezoid_integral(zs, inv_e)
    e = 1.0 / inv_e[-1]
    d_h = inv_e[-1]
    d_v = (z * d_m * d_m * d_h) ** (1.0 / 3.0)
    return {"z": z, "E": e, "D_H_unit": d_h, "D_M_unit": d_m, "D_V_unit": d_v}


def build_distance_rows() -> tuple[dict, list[dict]]:
    constants, radion = master_branch_background()
    z_values = [round(0.05 * i, 3) for i in range(0, 51)]
    return constants, [distance_row(z, constants, radion) for z in z_values]


def build_payload() -> dict:
    constants, distance_rows = build_distance_rows()
    targets = [
        {
            "name": "H_Janus_Holst(z)",
            "role": "background expansion for BAO and CMB distances",
            "ready": True,
            "required_inputs": [
                "Holst/radion background stress tensor",
                "matter/radiation continuity through the membrane",
                "early-time radiation branch",
            ],
        },
        {"name": "D_H(z)", "role": "radial BAO observable", "ready": True, "required_inputs": ["H_Janus_Holst(z)"]},
        {
            "name": "D_M(z)",
            "role": "transverse BAO observable",
            "ready": True,
            "required_inputs": ["H_Janus_Holst(z)", "Janus spatial-curvature/sign convention"],
        },
        {"name": "D_V(z)", "role": "isotropic BAO observable", "ready": True, "required_inputs": ["D_H(z)", "D_M(z)"]},
        {
            "name": "r_star_or_r_d",
            "role": "sound horizon or Janus replacement ruler",
            "ready": False,
            "required_inputs": ["baryon-photon sound speed", "Janus early-time expansion", "recombination/drag epoch map"],
        },
        {"name": "theta_star", "role": "CMB acoustic angular scale", "ready": False, "required_inputs": ["D_A(z_star)", "r_star_or_r_d"]},
    ]
    return {
        "description": "Target map for deriving Janus/Holst distances and the acoustic ruler without LambdaCDM compression.",
        "status": "janus-holst-late-distance-map-derived-sound-ruler-open",
        "branch": constants,
        "sample_distances": [distance_rows[0], distance_rows[len(distance_rows) // 2], distance_rows[-1]],
        "late_distance_targets_ready": True,
        "all_distance_targets_ready": False,
        "bao_shape_diagnostic_unblocked": True,
        "bao_shape_diagnostic_is_consistency_check_only": True,
        "bao_likelihood_unblocked": False,
        "cmb_likelihood_unblocked": False,
        "forbidden_shortcuts": [
            "Do not use Planck base-LambdaCDM Omega_m/H0/sigma8 as a Janus verdict.",
            "Do not use LCDM H(z) inside Janus BAO predictions.",
            "Do not fit an arbitrary BAO ruler after claiming no-fit.",
        ],
        "targets": targets,
        "next_derivation_order": [
            "derive H_Janus_Holst(z)",
            "derive D_H(z), D_M(z), D_V(z)",
            "derive r_star_or_r_d",
            "connect DESI BAO",
            "connect direct CMB acoustic/lensing observables",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Janus Holst Distance Ruler Map",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Late distance targets ready: {payload['late_distance_targets_ready']}",
        f"All distance targets ready: {payload['all_distance_targets_ready']}",
        f"BAO shape diagnostic unblocked: {payload['bao_shape_diagnostic_unblocked']}",
        f"BAO likelihood unblocked: {payload['bao_likelihood_unblocked']}",
        f"CMB likelihood unblocked: {payload['cmb_likelihood_unblocked']}",
        "",
        "## Targets",
        "",
        "| target | role | ready | required inputs |",
        "|---|---|---:|---|",
    ]
    for row in payload["targets"]:
        lines.append(f"| {row['name']} | {row['role']} | {row['ready']} | {', '.join(row['required_inputs'])} |")
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Next Derivation Order", ""])
    lines.extend(f"{index}. {item}" for index, item in enumerate(payload["next_derivation_order"], start=1))
    lines.extend(["", "## Distance Samples", "", "| z | E | D_H_unit | D_M_unit | D_V_unit |", "|---:|---:|---:|---:|---:|"])
    for row in payload["sample_distances"]:
        lines.append(
            f"| {row['z']:.3f} | {row['E']:.6g} | {row['D_H_unit']:.6g} | "
            f"{row['D_M_unit']:.6g} | {row['D_V_unit']:.6g} |"
        )
    lines.append("")
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    _, rows = build_distance_rows()
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
