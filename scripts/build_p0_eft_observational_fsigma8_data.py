from __future__ import annotations

from pathlib import Path
import csv
import json
import math
import urllib.request


BASE_URL = "https://svn.sdss.org/public/data/eboss/DR16cosmo/tags/v1_0_0/likelihoods/BAO-plus/"
RAW_DIR = Path("data/raw/sdss_dr16_bao_plus")
OUT_DIR = Path("data/processed/p0_eft_fsigma8")
REPORT_PATH = Path("outputs/reports/p0_eft_observational_fsigma8_data.md")
JSON_PATH = Path("outputs/reports/p0_eft_observational_fsigma8_data.json")
CSV_PATH = OUT_DIR / "sdss_dr16_fsigma8_points.csv"

DATASETS = [
    ("SDSS_MGS", "sdss_MGS_FSBAO_DVfs8.txt", "sdss_MGS_FSBAO_DVfs8_covtot.txt"),
    ("BOSS_DR12_LRG", "sdss_DR12_LRG_FSBAO_DMDHfs8.txt", "sdss_DR12_LRG_FSBAO_DMDHfs8_covtot.txt"),
    ("eBOSS_DR16_LRG", "sdss_DR16_LRG_FSBAO_DMDHfs8.txt", "sdss_DR16_LRG_FSBAO_DMDHfs8_covtot.txt"),
    ("eBOSS_DR16_QSO", "sdss_DR16_QSO_FSBAO_DMDHfs8.txt", "sdss_DR16_QSO_FSBAO_DMDHfs8_covtot.txt"),
]


def fetch_file(filename: str) -> Path:
    RAW_DIR.mkdir(parents=True, exist_ok=True)
    path = RAW_DIR / filename
    if not path.exists():
        urllib.request.urlretrieve(BASE_URL + filename, path)
    return path


def parse_vector(path: Path) -> list[dict]:
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        parts = line.split()
        rows.append({"z": float(parts[0]), "value": float(parts[1]), "label": parts[2]})
    return rows


def parse_cov(path: Path) -> list[list[float]]:
    return [
        [float(value) for value in line.split()]
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def extract_fsigma8_points() -> list[dict]:
    points = []
    for name, vector_file, cov_file in DATASETS:
        vector_path = fetch_file(vector_file)
        cov_path = fetch_file(cov_file)
        vector = parse_vector(vector_path)
        cov = parse_cov(cov_path)
        for index, row in enumerate(vector):
            if row["label"] == "f_sigma8":
                sigma = math.sqrt(cov[index][index])
                points.append(
                    {
                        "dataset": name,
                        "z": row["z"],
                        "fsigma8": row["value"],
                        "sigma": sigma,
                        "source_vector": str(vector_path),
                        "source_covariance": str(cov_path),
                    }
                )
    return sorted(points, key=lambda row: row["z"])


def build_payload() -> dict:
    points = extract_fsigma8_points()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(points[0].keys()))
        writer.writeheader()
        writer.writerows(points)
    return {
        "description": "Local observational f_sigma8 points extracted from official SDSS DR16 BAO+ likelihood files.",
        "status": "sdss-dr16-fsigma8-points-ready",
        "source_url": BASE_URL,
        "point_count": len(points),
        "redshift_range": [points[0]["z"], points[-1]["z"]],
        "csv": str(CSV_PATH),
        "points": points,
        "not_included": {
            "SDSS_DR16_ELG": "provided as grid likelihood, not reduced here to a Gaussian f_sigma8 point",
            "DESI": "not included as a local f_sigma8 covariance table in this repo yet",
            "Planck": "sigma8 prior is not a direct low-z f_sigma8 point for this curve",
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Observational f_sigma8 Data",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source URL: {payload['source_url']}",
        f"Point count: {payload['point_count']}",
        f"CSV: {payload['csv']}",
        "",
        "## Points",
        "",
        "| dataset | z | f_sigma8 | sigma |",
        "|---|---:|---:|---:|",
    ]
    for row in payload["points"]:
        lines.append(f"| {row['dataset']} | {row['z']:.3f} | {row['fsigma8']:.6g} | {row['sigma']:.6g} |")
    lines.extend(["", "## Not Included"])
    lines.extend(f"- {key}: {value}" for key, value in payload["not_included"].items())
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
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
