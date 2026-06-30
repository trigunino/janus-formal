from __future__ import annotations

from pathlib import Path
import csv
import json

try:
    from scripts.build_p0_eft_cosmological_chi2_calculator import (
        DATA_PATH,
        chi2_for_amplitude,
        read_csv,
    )
    from scripts.build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        integrate_growth,
        integrate_radion,
    )
except ModuleNotFoundError:
    from build_p0_eft_cosmological_chi2_calculator import (
        DATA_PATH,
        chi2_for_amplitude,
        read_csv,
    )
    from build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        integrate_growth,
        integrate_radion,
    )


REPORT_PATH = Path("outputs/reports/p0_eft_uv_initial_condition_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_uv_initial_condition_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_uv_initial_condition_scan.csv")


def curve_for_branch(growth_slope_initial: float) -> list[dict]:
    mpl2 = 64.0
    eps = -1.0
    h2 = 0.5
    omega_ds = 0.4
    rho_ds = omega_ds * 3.0 * mpl2 * h2
    constants = branch_constants(mpl2=mpl2, eps=eps, h2=h2, rho_ds=rho_ds)
    radion = integrate_radion(constants)
    omega_m0 = 0.32858131625099485
    growth = integrate_growth(constants, radion, omega_m0=omega_m0, growth_slope_initial=growth_slope_initial)
    return [{**row, "z": 1.0 / row["a"] - 1.0} for row in growth if 0.0 <= 1.0 / row["a"] - 1.0 <= 2.0]


def score_slope(data: list[dict], slope: float) -> dict:
    curve = curve_for_branch(slope)
    return {
        "growth_slope_initial": slope,
        "chi2_unit": chi2_for_amplitude(data, curve, 1.0),
    }


def run_scan() -> dict:
    data = read_csv(DATA_PATH)
    slopes = [round(0.2 + 0.05 * i, 3) for i in range(57)]
    rows = [score_slope(data, slope) for slope in slopes]
    best = min(rows, key=lambda row: row["chi2_unit"])
    accepted = [row for row in rows if row["chi2_unit"] < 15.0]
    return {
        "description": "UV initial growth-slope scan for the best spinor-torsion branch.",
        "status": "uv-initial-condition-scan-computed",
        "rows": rows,
        "best": best,
        "accepted_count": len(accepted),
        "accepted_best": min(accepted, key=lambda row: row["chi2_unit"]) if accepted else None,
        "criteria": "chi2_unit < 15",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT UV Initial Condition Scan",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Accepted count: {payload['accepted_count']}",
        f"Criteria: {payload['criteria']}",
        "",
        "## Best",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["best"].items())
    lines.extend(["", "## Accepted Best"])
    if payload["accepted_best"]:
        lines.extend(f"- {key}: {value}" for key, value in payload["accepted_best"].items())
    else:
        lines.append("- none")
    lines.append("")
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, csv_path: Path = CSV_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = run_scan()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(payload["rows"][0].keys()))
        writer.writeheader()
        writer.writerows(payload["rows"])
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
