from __future__ import annotations

from pathlib import Path
import csv
import json
import math


DATA_PATH = Path("data/processed/kids1000_s8_constraints.csv")
PLANCK_PRIOR_PATH = Path("data/processed/planck2018_base_lcdm_priors.csv")
REPORT_PATH = Path("outputs/reports/kids1000_s8_target.md")
JSON_PATH = Path("outputs/reports/kids1000_s8_target.json")


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def symmetric_error(row: dict[str, str]) -> float:
    return 0.5 * (float(row["s8_err_plus"]) + float(row["s8_err_minus"]))


def planck_s8_reference(path: Path = PLANCK_PRIOR_PATH) -> dict[str, float]:
    priors = {row["parameter"]: row for row in read_csv(path)}
    omega_m = float(priors["Omega_m"]["mean"])
    omega_m_sigma = float(priors["Omega_m"]["sigma"])
    sigma8 = float(priors["sigma8"]["mean"])
    sigma8_sigma = float(priors["sigma8"]["sigma"])
    s8 = sigma8 * math.sqrt(omega_m / 0.3)
    ds8_dsigma8 = math.sqrt(omega_m / 0.3)
    ds8_domega = sigma8 / (2.0 * math.sqrt(0.3 * omega_m))
    sigma = math.sqrt((ds8_dsigma8 * sigma8_sigma) ** 2 + (ds8_domega * omega_m_sigma) ** 2)
    return {"s8": s8, "sigma": sigma}


def build_payload() -> dict:
    rows = read_csv(DATA_PATH)
    planck = planck_s8_reference()
    targets = []
    for row in rows:
        s8 = float(row["s8"])
        sigma = symmetric_error(row)
        delta_vs_planck = planck["s8"] - s8
        combined_sigma = math.sqrt(planck["sigma"] ** 2 + sigma**2)
        targets.append(
            {
                "survey_id": row["survey_id"],
                "probe": row["probe"],
                "observable": row["observable"],
                "statistic": row["statistic"],
                "s8": s8,
                "s8_err_plus": float(row["s8_err_plus"]),
                "s8_err_minus": float(row["s8_err_minus"]),
                "s8_sigma_symmetric": sigma,
                "reference": row["reference"],
                "source_url": row["source_url"],
                "products_url": row["products_url"],
                "delta_vs_planck2018_s8": delta_vs_planck,
                "pull_vs_planck2018_s8": delta_vs_planck / combined_sigma,
                "notes": row["notes"],
            }
        )
    return {
        "description": "KiDS-1000 compressed S8 target for the Janus weak-lensing hard test.",
        "status": "compressed-s8-target-ready",
        "observable": "S8 = sigma8 * sqrt(Omega_m / 0.3)",
        "planck2018_reference": planck,
        "targets": targets,
        "n_fit_parameters": 0,
        "compressed_target_ready": True,
        "full_survey_likelihood_ready": False,
        "missing_for_full_likelihood": [
            "KiDS data vector",
            "KiDS covariance matrix",
            "KiDS n(z) tomographic distributions",
            "KiDS mask/window treatment",
            "nuisance parameter policy",
        ],
        "verdict": (
            "Use KiDS-1000 as a low-S8 compressed target now; do not call this a full "
            "cosmic-shear likelihood until the public data products are loaded."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 S8 Target",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Observable: `{payload['observable']}`",
        f"Planck 2018 reference S8: `{payload['planck2018_reference']['s8']:.6g}` "
        f"+/- `{payload['planck2018_reference']['sigma']:.3g}`",
        "",
        "| survey | probe | statistic | S8 | sigma sym | pull vs Planck2018 | source |",
        "|---|---|---|---:|---:|---:|---|",
    ]
    for row in payload["targets"]:
        lines.append(
            f"| {row['survey_id']} | {row['probe']} | {row['statistic']} | "
            f"{row['s8']:.6g} +{row['s8_err_plus']:.3g}/-{row['s8_err_minus']:.3g} | "
            f"{row['s8_sigma_symmetric']:.3g} | {row['pull_vs_planck2018_s8']:.3g} | "
            f"{row['source_url']} |"
        )
    lines.extend(
        [
            "",
            f"Compressed target ready: `{payload['compressed_target_ready']}`",
            f"Full survey likelihood ready: `{payload['full_survey_likelihood_ready']}`",
            "",
            "Missing for full likelihood:",
        ]
    )
    lines.extend(f"- {item}" for item in payload["missing_for_full_likelihood"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
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
