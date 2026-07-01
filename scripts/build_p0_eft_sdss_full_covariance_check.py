from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_cosmological_chi2_calculator import (
        DATA_PATH,
        COV_PATH,
        best_amplitude_full_cov,
        build_residuals,
        chi2_for_amplitude_full_cov,
        read_covariance,
        read_csv,
    )
    from scripts.run_p0_eft_holst_membrane_co_optimisation import branch_curve
except ModuleNotFoundError:
    from build_p0_eft_cosmological_chi2_calculator import (
        DATA_PATH,
        COV_PATH,
        best_amplitude_full_cov,
        build_residuals,
        chi2_for_amplitude_full_cov,
        read_covariance,
        read_csv,
    )
    from run_p0_eft_holst_membrane_co_optimisation import branch_curve


REPORT_PATH = Path("outputs/reports/p0_eft_sdss_full_covariance_check.md")
JSON_PATH = Path("outputs/reports/p0_eft_sdss_full_covariance_check.json")


def build_payload() -> dict:
    data = read_csv(DATA_PATH)
    covariance = read_covariance(COV_PATH)
    branch, curve = branch_curve(eta_holst=-2.0, z_sigma=0.5)
    amp_best = best_amplitude_full_cov(data, curve, covariance)
    chi2_unit = chi2_for_amplitude_full_cov(data, curve, 1.0, covariance)
    chi2_best = chi2_for_amplitude_full_cov(data, curve, amp_best, covariance)
    residuals = build_residuals(data, curve, amp_best)
    dof_best = len(data) - 1
    return {
        "description": "SDSS/eBOSS DR16 f_sigma8 full-covariance check for the Holst membrane branch.",
        "status": "sdss-full-covariance-computed",
        "data_path": str(DATA_PATH),
        "covariance_path": str(COV_PATH),
        "branch": branch,
        "data_points": len(data),
        "chi2_unit_amplitude_full_covariance": chi2_unit,
        "amplitude_best_full_covariance": amp_best,
        "chi2_best_amplitude_full_covariance": chi2_best,
        "dof_best_amplitude": dof_best,
        "reduced_chi2_best_full_covariance": chi2_best / dof_best,
        "residuals_best_amplitude": residuals,
        "notes": [
            "Uses the reduced 5x5 f_sigma8 covariance extracted from SDSS/eBOSS DR16 BAO-plus likelihood files.",
            "The BOSS DR12 z=0.38 and z=0.51 f_sigma8 points retain their published cross-covariance.",
            "DESI, Planck and weak-lensing likelihoods are not included in this check.",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT SDSS Full Covariance Check",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Data points: {payload['data_points']}",
        f"Chi2 A=1 full covariance: {payload['chi2_unit_amplitude_full_covariance']:.6g}",
        f"Best amplitude full covariance: {payload['amplitude_best_full_covariance']:.6g}",
        f"Chi2 best full covariance: {payload['chi2_best_amplitude_full_covariance']:.6g}",
        f"Reduced chi2 best full covariance: {payload['reduced_chi2_best_full_covariance']:.6g}",
        "",
        "## Branch",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["branch"].items())
    lines.extend(["", "## Residuals", "", "| dataset | z | data | model | sigma | pull |", "|---|---:|---:|---:|---:|---:|"])
    for row in payload["residuals_best_amplitude"]:
        lines.append(
            f"| {row['dataset']} | {row['z']:.3f} | {row['data']:.6g} | "
            f"{row['janus_model']:.6g} | {row['sigma']:.6g} | {row['pull']:.3f} |"
        )
    lines.extend(["", "## Notes"])
    lines.extend(f"- {note}" for note in payload["notes"])
    lines.append("")
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
