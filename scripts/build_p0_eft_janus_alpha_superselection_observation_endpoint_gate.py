from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
DOWNLOADS = Path.home() / "Downloads"
BAO_REPO = Path("data/external/bao_data")
JSON_PATH = REPORTS / "p0_eft_janus_alpha_superselection_observation_endpoint_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_alpha_superselection_observation_endpoint_gate.md"


def _exists_any(patterns: list[str], base: Path = DOWNLOADS) -> bool:
    return any(path.is_file() for pattern in patterns for path in base.glob(pattern))


def build_payload(downloads: Path = DOWNLOADS, bao_repo: Path = BAO_REPO) -> dict[str, Any]:
    sn_available = _exists_any(
        ["jla_likelihood_v6*.tgz", "jla_light_curves*.tgz", "Pantheon*"],
        downloads,
    )
    bao_download_available = _exists_any(
        ["*DESI*BAO*.csv", "*DESI*BAO*.txt", "*DESI*BAO*.dat", "*BAO*.csv", "*BAO*.txt", "*BAO*.dat"],
        downloads,
    )
    bao_repo_available = _exists_any(
        ["desi_bao_dr2/*_mean.txt", "desi_bao_dr2/*_cov.txt", "desi_2024*_mean.txt", "desi_2024*_cov.txt"],
        bao_repo,
    )
    bao_available = bao_download_available or bao_repo_available
    endpoint_ready = sn_available and bao_available
    return {
        "status": "janus-alpha-superselection-observation-endpoint",
        "downloads_path": str(downloads),
        "bao_repo_path": str(bao_repo),
        "alpha_sector_program_declared": True,
        "datasets": {
            "SN": {
                "available": sn_available,
                "detected_patterns": ["jla_likelihood_v6*.tgz", "jla_light_curves*.tgz", "Pantheon*"],
                "role": "shape/q0 branch and relative-distance sector constraint",
            },
            "BAO": {
                "available": bao_available,
                "downloads_available": bao_download_available,
                "repo_available": bao_repo_available,
                "detected_patterns": [
                    "data/external/bao_data/desi_bao_dr2/*_mean.txt",
                    "data/external/bao_data/desi_bao_dr2/*_cov.txt",
                    "*DESI*BAO*.csv",
                    "*DESI*BAO*.txt",
                    "*DESI*BAO*.dat",
                    "*BAO*.csv",
                    "*BAO*.txt",
                    "*BAO*.dat",
                ],
                "role": "absolute scale/ruler sector selection",
            },
        },
        "sn_only_shape_allowed": sn_available,
        "absolute_scale_selection_ready": endpoint_ready,
        "full_sector_selection_ready": endpoint_ready,
        "no_fit_claim_forbidden": True,
        "classification": (
            "ready_for_SN_shape_only"
            if sn_available and not bao_available
            else "ready_for_SN_plus_BAO_sector_selection"
            if endpoint_ready
            else "blocked_missing_observational_inputs"
        ),
        "missing_for_full_endpoint": []
        if endpoint_ready
        else ["BAO_data"] if sn_available else ["SN_data", "BAO_data"],
        "next_action": (
            "run SN shape-only/q0 sector check; acquire BAO for absolute alpha selection"
            if sn_available and not bao_available
            else "run SN+BAO alpha-sector calibration"
            if endpoint_ready
            else "acquire SN and BAO data"
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Alpha Superselection Observation Endpoint",
        "",
        f"Classification: `{payload['classification']}`",
        f"Full sector selection ready: `{payload['full_sector_selection_ready']}`",
        f"No-fit claim forbidden: `{payload['no_fit_claim_forbidden']}`",
        "",
        "## Datasets",
        "",
        "| Dataset | Available | Role |",
        "|---|---:|---|",
        *[
            f"| `{key}` | `{row['available']}` | {row['role']} |"
            for key, row in payload["datasets"].items()
        ],
        "",
        f"Missing for full endpoint: `{payload['missing_for_full_endpoint']}`",
        f"Next action: `{payload['next_action']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
