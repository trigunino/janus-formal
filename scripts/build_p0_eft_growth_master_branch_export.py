from __future__ import annotations

from pathlib import Path
import csv
import json

import matplotlib.pyplot as plt

try:
    from scripts.build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        derived_omega_m0,
        integrate_growth,
        integrate_radion,
    )
except ModuleNotFoundError:
    from build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        derived_omega_m0,
        integrate_growth,
        integrate_radion,
    )


REPORT_PATH = Path("outputs/reports/p0_eft_growth_master_branch_export.md")
JSON_PATH = Path("outputs/reports/p0_eft_growth_master_branch_export.json")
CSV_PATH = Path("outputs/reports/p0_eft_growth_master_branch_z0_2.csv")
PNG_PATH = Path("outputs/reports/p0_eft_growth_master_branch_z0_2.png")


def master_constants() -> dict:
    mpl2 = 4.0
    eps = -1.0
    h2 = 0.5
    omega_ds = 0.05
    return branch_constants(mpl2=mpl2, eps=eps, h2=h2, rho_ds=omega_ds * 3.0 * mpl2 * h2)


def build_curve() -> tuple[dict, list[dict]]:
    constants = master_constants()
    radion = integrate_radion(constants)
    omega_m0 = derived_omega_m0(constants, radion)
    growth = integrate_growth(constants, radion)
    z_rows = []
    for row in growth:
        z = 1.0 / row["a"] - 1.0
        if 0.0 <= z <= 2.0:
            z_rows.append({**row, "z": z})
    constants = {**constants, "Omega_m0": omega_m0, "Omega_T0": radion[-1]["Omega_T"]}
    return constants, z_rows


def render_plot(rows: list[dict], png_path: Path = PNG_PATH) -> None:
    png_path.parent.mkdir(parents=True, exist_ok=True)
    z = [row["z"] for row in rows]
    fs8 = [row["fsigma8_shape"] for row in rows]
    mu = [row["mu"] for row in rows]
    fig, ax1 = plt.subplots(figsize=(7, 4))
    ax1.plot(z, fs8, label="fsigma8_shape", color="#1f77b4")
    ax1.set_xlabel("z")
    ax1.set_ylabel("fsigma8_shape")
    ax1.invert_xaxis()
    ax2 = ax1.twinx()
    ax2.plot(z, mu, label="mu(k=1,a)", color="#d62728", alpha=0.75)
    ax2.set_ylabel("mu")
    ax1.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(png_path, dpi=160)
    plt.close(fig)


def build_payload() -> dict:
    constants, rows = build_curve()
    render_plot(rows)
    samples = [rows[0], rows[len(rows) // 2], rows[-1]]
    theorem_status = {
        "physical_branch_selected": True,
        "friedmann_matter_positive": constants["Omega_m0"] > 0.05,
        "z0_to_z2_curve_exported": True,
        "plot_exported": PNG_PATH.exists(),
        "observational_fsigma8_table_loaded": False,
        "direct_planck_sdss_eboss_desi_comparison_done": False,
        "full_cosmology_prediction_ready": False,
    }
    return {
        "description": "Production export for the first physical EC Janus growth branch.",
        "status": "master-branch-growth-exported-no-observation-comparison",
        "branch": constants,
        "samples": samples,
        "outputs": {"csv": str(CSV_PATH), "png": str(PNG_PATH)},
        "theorem_status": theorem_status,
        "verdict": (
            "The first physical branch is numerically exported for z in [0,2]. Full "
            "observational comparison remains open because no local f_sigma8 data table "
            "is loaded in the repository."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Growth Master Branch Export",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Branch",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["branch"].items())
    lines.extend(["", "## Outputs"])
    lines.extend(f"- {key}: {value}" for key, value in payload["outputs"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Samples"])
    for row in payload["samples"]:
        lines.append(
            f"- z={row['z']:.6g}, a={row['a']:.6g}, Omega_T={row['Omega_T']:.6g}, "
            f"mu={row['mu']:.6g}, fsigma8_shape={row['fsigma8_shape']:.6g}"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, csv_path: Path = CSV_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    _, rows = build_curve()
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")
    print(f"Wrote {PNG_PATH}")


if __name__ == "__main__":
    main()
