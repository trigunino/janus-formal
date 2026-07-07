from __future__ import annotations

import csv
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
for path in (ROOT, SRC):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from janus_lab.data import load_desi_bao, load_pantheon_diag


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_observation_data_inventory.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_observation_data_inventory.json")

DATASETS = {
    "desi_dr2_bao": [
        Path("data/raw/desi_dr2/desi_gaussian_bao_ALL_GCcomb_mean.txt"),
        Path("data/raw/desi_dr2/desi_gaussian_bao_ALL_GCcomb_cov.txt"),
    ],
    "pantheon_plus_diag": [
        Path("data/raw/pantheon_plus/Pantheon+SH0ES.dat"),
        Path("data/raw/pantheon_plus/Pantheon+SH0ES_STAT+SYS.cov"),
    ],
    "sdss_dr16_fsigma8": [
        Path("data/processed/p0_eft_fsigma8/sdss_dr16_fsigma8_points.csv"),
        Path("data/processed/p0_eft_fsigma8/sdss_dr16_fsigma8_covariance.csv"),
    ],
    "kids1000_s8": [
        Path("data/processed/kids1000_s8_constraints.csv"),
    ],
    "planck2018_priors": [
        Path("data/processed/planck2018_base_lcdm_priors.csv"),
    ],
}


def _sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _csv_rows(path: Path) -> int | None:
    if not path.exists():
        return None
    with path.open("r", encoding="utf-8", newline="") as handle:
        return sum(1 for _ in csv.reader(handle))


def _dataset_status(name: str, paths: list[Path]) -> dict[str, Any]:
    files = [
        {
            "path": str(path),
            "exists": path.exists(),
            "sha256": _sha256(path),
        }
        for path in paths
    ]
    payload: dict[str, Any] = {
        "name": name,
        "files": files,
        "all_files_present": all(item["exists"] for item in files),
        "raw_data_reusable_for_Z2Sigma": True,
        "existing_model_scores_reusable_for_Z2Sigma": False,
        "sector_to_observable_map_available": False,
    }
    if name == "desi_dr2_bao" and payload["all_files_present"]:
        dataset = load_desi_bao(paths[0], paths[1])
        payload.update(
            {
                "data_points": int(len(dataset.value)),
                "quantities": sorted(set(str(item) for item in dataset.quantity)),
                "covariance_shape": list(dataset.covariance.shape),
            }
        )
    elif name == "pantheon_plus_diag" and paths[0].exists():
        dataset = load_pantheon_diag(paths[0])
        payload.update({"data_points": int(len(dataset.z)), "uses_full_covariance": False})
    else:
        row_counts = [_csv_rows(path) for path in paths if path.suffix.lower() == ".csv"]
        if row_counts:
            payload["csv_row_counts"] = row_counts
    return payload


def build_payload() -> dict[str, Any]:
    datasets = {name: _dataset_status(name, paths) for name, paths in DATASETS.items()}
    reusable = [
        name
        for name, payload in datasets.items()
        if payload["all_files_present"] and payload["raw_data_reusable_for_Z2Sigma"]
    ]
    return {
        "status": "janus-z2-sigma-observation-data-inventory",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Inventories local observational data that can be reused as data only. "
            "Legacy Holst/Z4/EFT scores are not imported as Z2/Sigma evidence. "
            "A sector-to-observable map is still required before testing N_gap."
        ),
        "datasets": datasets,
        "reusable_raw_datasets": reusable,
        "observation_data_inventory_ready": bool(reusable),
        "sector_observable_map_derived": False,
        "trial_can_run_now": False,
        "next_required": [
            "derive Z2/Sigma sector-to-observable map",
            "choose a non-overlapping dataset vector",
            "then run fixed-sector observation trial without continuous R_s fit",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Observation Data Inventory",
        "",
        payload["physical_statement"],
        "",
        f"Inventory ready: `{payload['observation_data_inventory_ready']}`",
        f"Trial can run now: `{payload['trial_can_run_now']}`",
        "",
        "## Reusable Raw Datasets",
    ]
    lines.extend(f"- `{name}`" for name in payload["reusable_raw_datasets"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- {item}" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
