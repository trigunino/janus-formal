from __future__ import annotations

from pathlib import Path
import csv
import json

try:
    from scripts.build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        derived_omega_m0,
        integrate_radion,
    )
except ModuleNotFoundError:
    from build_p0_eft_growth_no_fit_numerical_export import (
        branch_constants,
        derived_omega_m0,
        integrate_radion,
    )


REPORT_PATH = Path("outputs/reports/p0_eft_physical_branch_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_physical_branch_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_physical_branch_scan.csv")


def evaluate_branch(mpl2: float, eps: float, omega_ds: float) -> dict:
    h2 = 0.5
    rho_ds = omega_ds * 3.0 * mpl2 * h2
    try:
        constants = branch_constants(mpl2=mpl2, eps=eps, h2=h2, rho_ds=rho_ds)
        radion = integrate_radion(constants)
        omega_m0 = derived_omega_m0(constants, radion)
        omega_t0 = radion[-1]["Omega_T"]
        ok = omega_m0 > 0.05
        reason = "ok" if ok else "nonpositive-or-too-small-matter"
    except ValueError as exc:
        constants = {"ratio": None, "chi_inf": None, "Lambda_J": None}
        omega_m0 = None
        omega_t0 = None
        ok = False
        reason = str(exc)
    return {
        "eps": eps,
        "Mpl2": mpl2,
        "Omega_dS_residual": omega_ds,
        "ratio": constants["ratio"],
        "chi_inf": constants["chi_inf"],
        "Lambda_J": constants["Lambda_J"],
        "Omega_T0": omega_t0,
        "Omega_m0": omega_m0,
        "physical": ok,
        "reason": reason,
    }


def scan_branches() -> dict:
    rows = []
    for eps in (-1.0, 1.0):
        for mpl2 in (4.0, 6.0, 8.0, 12.0, 16.0, 24.0, 32.0, 48.0, 64.0):
            for omega_ds in (0.05, 0.1, 0.2, 0.4, 0.7, 1.0):
                rows.append(evaluate_branch(mpl2, eps, omega_ds))
    physical = [row for row in rows if row["physical"]]
    first = physical[0] if physical else None
    return {
        "description": "Scan of EC Janus physical Friedmann branches.",
        "status": "physical-branch-found" if first else "no-physical-branch-found",
        "criteria": "atanh domain valid and Omega_m0 > 0.05",
        "rows": rows,
        "physical_count": len(physical),
        "first_physical_branch": first,
        "verdict": (
            "The original eps=+1, Mpl2=4, Omega_dS=1 branch is excluded, but nearby "
            "branches with reduced dS residual or larger Mpl2 can restore positive matter."
            if first
            else "No branch in the scanned grid restores positive matter."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Physical Branch Scan",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Criteria: {payload['criteria']}",
        f"Physical count: {payload['physical_count']}",
        "",
        "## First Physical Branch",
    ]
    first = payload["first_physical_branch"]
    if first:
        lines.extend(f"- {key}: {value}" for key, value in first.items())
    else:
        lines.append("- none")
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, csv_path: Path = CSV_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = scan_branches()
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
