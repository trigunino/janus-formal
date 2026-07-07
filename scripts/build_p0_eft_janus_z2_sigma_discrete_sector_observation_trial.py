from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_discrete_family_propagation import (
    build_payload as discrete_family,
)
from scripts.build_p0_eft_janus_z2_sigma_discrete_sector_observation_readiness_gate import (
    build_payload as readiness,
)
from scripts.build_p0_eft_janus_z2_sigma_observation_data_inventory import (
    build_payload as data_inventory,
)
from scripts.build_p0_eft_janus_z2_sigma_ngap_to_background_source_frontier import (
    build_payload as background_frontier,
)


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "discrete_sector_observation_trial_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_sector_observation_trial.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_sector_observation_trial.json")

FORBIDDEN_PROVENANCE = ("continuous_fit", "retune", "legacy_z4", "mock_pass")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_PROVENANCE)


def _finite(value: Any) -> float | None:
    if not isinstance(value, (int, float)):
        return None
    value = float(value)
    return value if math.isfinite(value) else None


def _channels(data: dict[str, Any]) -> list[dict[str, Any]]:
    raw = data.get("channels")
    return [item for item in raw if isinstance(item, dict)] if isinstance(raw, list) else []


def _range_pass(value: float, channel: dict[str, Any]) -> bool:
    low = _finite(channel.get("min"))
    high = _finite(channel.get("max"))
    return (low is None or value >= low) and (high is None or value <= high)


def _chi2(value: float, channel: dict[str, Any]) -> float:
    target = _finite(channel.get("target"))
    sigma = _finite(channel.get("sigma"))
    weight = _finite(channel.get("weight")) or 1.0
    if target is None or sigma is None or sigma <= 0.0:
        return 0.0
    return weight * ((value - target) / sigma) ** 2


def _evaluate_sector(entry: dict[str, Any], channels: list[dict[str, Any]]) -> dict[str, Any]:
    rows = []
    total_chi2 = 0.0
    for channel in channels:
        key = str(channel.get("observable_key", ""))
        if key not in entry:
            rows.append({"name": channel.get("name", key), "observable_key": key, "passed": False, "reason": "missing_observable"})
            total_chi2 += math.inf
            continue
        value = float(entry[key])
        passed = _range_pass(value, channel)
        chi2 = _chi2(value, channel)
        total_chi2 += chi2
        rows.append(
            {
                "name": channel.get("name", key),
                "observable_key": key,
                "value": value,
                "passed": passed,
                "chi2": chi2,
            }
        )
    return {
        "N_gap": entry["N_gap"],
        "channel_rows": rows,
        "chi2": total_chi2,
        "sector_survives": all(row["passed"] for row in rows),
    }


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    family = discrete_family()
    ready = readiness()
    inventory = data_inventory()
    background = background_frontier()
    channels = _channels(data)
    map_derived = bool(data.get("sector_observable_map_derived"))
    background_ready = bool(background["N_gap_to_background_source_ready"])
    contracts = {
        "discrete_family_propagation_ready": family["discrete_family_propagation_ready"],
        "observation_readiness_gate_passed": ready["observation_readiness"],
        "observation_data_inventory_ready": inventory["observation_data_inventory_ready"],
        "N_gap_to_background_source_or_external_map_ready": background_ready or map_derived,
        "sector_observable_map_derived": map_derived,
        "observational_data_vector_declared": bool(data.get("observational_data_vector_declared")),
        "non_overlap_accounting_declared": bool(data.get("non_overlap_accounting_declared")),
        "channels_declared": bool(channels),
        "continuous_fit_forbidden": not bool(data.get("continuous_fit_used")),
        "sector_relabeling_forbidden": not bool(data.get("sector_relabeling_used")),
        "legacy_Z4_input_forbidden": not bool(data.get("legacy_Z4_input_used")),
        "clean_provenance": not _bad_provenance(data.get("provenance")),
    }
    trial_ready = all(contracts.values())
    rows = [_evaluate_sector(item, channels) for item in family["sector_table"]] if trial_ready else []
    ranked = sorted(rows, key=lambda item: item["chi2"])
    survivors = [row["N_gap"] for row in rows if row["sector_survives"]]
    return {
        "status": "janus-z2-sigma-discrete-sector-observation-trial",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Runs fixed-sector observational rejection/ranking only after a derived "
            "sector-to-observable map exists. It never fits R_s, relabels N_gap, "
            "or imports legacy Z4 evidence."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "contracts": contracts,
        "reusable_raw_datasets": inventory["reusable_raw_datasets"],
        "missing_effective_primitives": background["missing_effective_primitives"],
        "trial_ready": trial_ready,
        "sector_rows": rows,
        "ranked_sectors_by_chi2": [{"N_gap": row["N_gap"], "chi2": row["chi2"]} for row in ranked],
        "surviving_sectors": survivors,
        "unique_sector_selected_by_trial": len(survivors) == 1,
        "unique_prediction_claim_allowed": False,
        "blocked_by": [key for key, ok in contracts.items() if not ok],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Discrete Sector Observation Trial",
        "",
        payload["physical_statement"],
        "",
        f"Trial ready: `{payload['trial_ready']}`",
        f"Survivors: `{payload['surviving_sectors']}`",
        f"Unique prediction claim allowed: `{payload['unique_prediction_claim_allowed']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
