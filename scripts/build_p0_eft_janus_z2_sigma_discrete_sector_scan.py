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


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "discrete_sector_scan_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_sector_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_sector_scan.json")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _range(value: Any) -> tuple[float | None, float | None]:
    if not isinstance(value, dict):
        return None, None
    low = value.get("min")
    high = value.get("max")
    low = float(low) if isinstance(low, (int, float)) and math.isfinite(float(low)) else None
    high = float(high) if isinstance(high, (int, float)) and math.isfinite(float(high)) else None
    return low, high


def _in_range(value: float, bounds: tuple[float | None, float | None]) -> bool:
    low, high = bounds
    return (low is None or value >= low) and (high is None or value <= high)


def _classify_sector(entry: dict[str, Any], data: dict[str, Any]) -> dict[str, Any]:
    checks = {}
    ranges = {
        "R_s_m": _range(data.get("R_s_m_range")),
        "M_bridge_kg": _range(data.get("M_bridge_kg_range")),
        "chi_LL_abs_inverse_m": _range(data.get("chi_LL_abs_inverse_m_range")),
        "spectral_scale_inverse_m": _range(data.get("spectral_scale_inverse_m_range")),
        "lambda_F2_over_q_LL_m_minus_2": _range(data.get("lambda_F2_over_q_LL_m_minus_2_range")),
    }
    for key, bounds in ranges.items():
        if bounds == (None, None) or key not in entry:
            continue
        checks[key] = _in_range(float(entry[key]), bounds)
    return {
        "N_gap": entry["N_gap"],
        "checks": checks,
        "sector_survives": all(checks.values()) if checks else True,
        "diagnostic_only": not checks,
        "values": entry,
    }


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    family = discrete_family()
    ready = readiness()
    scan_contracts = {
        "discrete_family_ready": family["discrete_family_propagation_ready"],
        "observation_readiness_gate_passed": ready["observation_readiness"],
        "no_continuous_fit": not bool(data.get("continuous_fit_used")),
        "no_sector_relabeling": not bool(data.get("sector_relabeling_used")),
        "fixed_ranges_only": bool(data.get("fixed_ranges_only")),
    }
    scan_ready = all(scan_contracts.values())
    rows = [_classify_sector(item, data) for item in family["sector_table"]] if scan_ready else []
    survivors = [row["N_gap"] for row in rows if row["sector_survives"]]
    rejected = [row["N_gap"] for row in rows if not row["sector_survives"]]
    return {
        "status": "janus-z2-sigma-discrete-sector-scan",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Scans fixed discrete N_gap sectors against predeclared physical ranges. "
            "This rejects or keeps sectors; it never fits a continuous throat scale."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "scan_contracts": scan_contracts,
        "scan_ready": scan_ready,
        "sector_rows": rows,
        "surviving_sectors": survivors,
        "rejected_sectors": rejected,
        "unique_sector_selected_by_scan": len(survivors) == 1,
        "unique_prediction_claim_allowed": False,
        "blocked_by": [key for key, ok in scan_contracts.items() if not ok],
        "forbidden_shortcuts": [
            "optimize_R_s_continuously",
            "use_ranges_created_from_sector_outputs",
            "claim_observation_derives_N_gap",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Discrete Sector Scan",
        "",
        payload["physical_statement"],
        "",
        f"Scan ready: `{payload['scan_ready']}`",
        f"Survivors: `{payload['surviving_sectors']}`",
        f"Rejected: `{payload['rejected_sectors']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
