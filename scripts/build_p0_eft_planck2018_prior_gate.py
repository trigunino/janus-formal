from __future__ import annotations

from pathlib import Path
import csv
import json

try:
    from scripts.run_p0_eft_holst_membrane_co_optimisation import branch_curve
except ModuleNotFoundError:
    from run_p0_eft_holst_membrane_co_optimisation import branch_curve


DATA_PATH = Path("data/processed/planck2018_base_lcdm_priors.csv")
REPORT_PATH = Path("outputs/reports/p0_eft_planck2018_prior_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_planck2018_prior_gate.json")


def read_priors(path: Path = DATA_PATH) -> dict[str, dict]:
    with path.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    return {
        row["parameter"]: {
            **row,
            "mean": float(row["mean"]),
            "sigma": float(row["sigma"]),
        }
        for row in rows
    }


def gaussian_pull(value: float, mean: float, sigma: float) -> float:
    return (value - mean) / sigma


def build_payload() -> dict:
    priors = read_priors()
    branch, _curve = branch_curve(eta_holst=-2.0, z_sigma=0.5)
    omega_prior = priors["Omega_m"]
    omega_pull = gaussian_pull(branch["Omega_m0"], omega_prior["mean"], omega_prior["sigma"])
    omega_chi2 = omega_pull * omega_pull
    return {
        "description": "Planck 2018 base-LambdaCDM-derived Omega_m stress test for the Holst/membrane branch.",
        "status": "planck2018-lcdm-derived-omega-m-stress-test-computed",
        "priors_path": str(DATA_PATH),
        "branch": branch,
        "Omega_m0_model": branch["Omega_m0"],
        "Omega_m_planck_mean": omega_prior["mean"],
        "Omega_m_planck_sigma": omega_prior["sigma"],
        "Omega_m_pull": omega_pull,
        "Omega_m_chi2": omega_chi2,
        "passes_lcdm_derived_3sigma_omega_m_stress_test": abs(omega_pull) < 3.0,
        "is_direct_janus_cmb_likelihood": False,
        "cmb_parameters_not_scored": ["H0", "sigma8", "A_s", "n_s", "theta_star", "C_ell"],
        "planck_full_likelihood_computed": False,
        "blocker": (
            "This is not a direct Janus-vs-Planck likelihood. The quoted Omega_m prior is "
            "inferred inside base LambdaCDM. A direct Janus CMB comparison requires Janus "
            "recombination distances, primordial amplitude, transfer functions, and CMB spectra."
        ),
        "source": "Planck 2018 results VI: H0=67.36+-0.54, Omega_m=0.3158+-0.0073 for TTTEEE+lowE+lensing; sigma8 summary 0.811+-0.006.",
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Planck 2018 LCDM-Derived Stress Test",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Omega_m model: {payload['Omega_m0_model']:.6g}",
            f"Omega_m Planck: {payload['Omega_m_planck_mean']:.6g} +/- {payload['Omega_m_planck_sigma']:.6g}",
            f"Omega_m pull: {payload['Omega_m_pull']:.3f} sigma",
            f"Omega_m chi2: {payload['Omega_m_chi2']:.6g}",
            f"Direct Janus CMB likelihood: {payload['is_direct_janus_cmb_likelihood']}",
            f"Passes LCDM-derived 3 sigma Omega_m stress test: {payload['passes_lcdm_derived_3sigma_omega_m_stress_test']}",
            f"Planck full likelihood computed: {payload['planck_full_likelihood_computed']}",
            "",
            "## Blocker",
            "",
            payload["blocker"],
            "",
            "## Source",
            "",
            payload["source"],
            "",
        ]
    )


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
