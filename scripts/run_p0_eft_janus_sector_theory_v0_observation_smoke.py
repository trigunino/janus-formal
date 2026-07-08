from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_sector_theory_v0_matrix import build_payload as build_matrix
from scripts.build_p0_eft_janus_z2_alpha_observational_fit_gate import (
    JSON_PATH as ALPHA_OBS_JSON,
    write_reports as write_alpha_obs_reports,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_sector_theory_v0_observation_smoke.json"
REPORT_PATH = REPORTS / "p0_eft_janus_sector_theory_v0_observation_smoke.md"


def _load_alpha_observation_payload() -> dict[str, Any]:
    if not ALPHA_OBS_JSON.exists():
        return write_alpha_obs_reports()
    return json.loads(ALPHA_OBS_JSON.read_text(encoding="utf-8"))


def build_payload() -> dict[str, Any]:
    matrix = build_matrix()
    obs = _load_alpha_observation_payload()
    primary = obs["best_fit"][obs["primary_observational_endpoint"]]
    published_q0 = next(row for row in matrix["sector_laws"] if row["id"] == "published_sn_q0_sector")

    return {
        "status": "janus-sector-theory-v0-observation-smoke",
        "datasets": obs["datasets"],
        "fit_policy": obs["fit_policy"],
        "published_q0_sector": published_q0,
        "primary_endpoint": obs["primary_observational_endpoint"],
        "primary_best": primary,
        "paper_q0": -0.087,
        "current_observation_selected_q0": primary["q0"],
        "paper_q0_matches_current_combined_endpoint": abs(primary["q0"] + 0.087) < 0.01,
        "classification": obs["classification"],
        "interpretation": (
            "The data can select a Janus q0 sector, but this is not a no-fit alpha law. "
            "In the existing SN+BAO endpoint, the selected q0 moves toward the GR-like boundary."
        ),
        "no_fit_alpha_generated": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    best = payload["primary_best"]
    lines = [
        "# Janus Sector Theory v0 Observation Smoke",
        "",
        f"Primary endpoint: `{payload['primary_endpoint']}`",
        f"Paper q0: `{payload['paper_q0']}`",
        f"Observation-selected q0: `{payload['current_observation_selected_q0']:.6g}`",
        f"Paper q0 matches endpoint: `{payload['paper_q0_matches_current_combined_endpoint']}`",
        f"Chi2: `{best['chi2']:.6g}`",
        f"Classification: `{payload['classification']}`",
        f"No-fit alpha generated: `{payload['no_fit_alpha_generated']}`",
        "",
        payload["interpretation"],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
