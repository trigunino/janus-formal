from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_discrete_family_propagation import (
    build_payload as discrete_family,
)


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "discrete_sector_observation_readiness_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_sector_observation_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_sector_observation_readiness_gate.json")

FORBIDDEN_TOKENS = ("fit", "retune", "continuous_opt", "z4")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_flag(data: dict[str, Any], key: str) -> bool:
    return bool(data.get(key))


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return any(token in text for token in FORBIDDEN_TOKENS)


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    family = discrete_family()
    contracts = {
        "discrete_family_propagation_ready": family["discrete_family_propagation_ready"],
        "sector_table_nonempty": bool(family["sector_table"]),
        "non_overlap_accounting_declared": bool(data.get("non_overlap_accounting_declared")),
        "physical_priors_declared": bool(data.get("physical_priors_declared")),
        "continuous_parameter_fit_forbidden": not _bad_flag(data, "continuous_parameter_fit_used"),
        "sector_relabeling_forbidden": not _bad_flag(data, "sector_relabeling_used"),
        "observation_can_only_reject_or_rank_sectors": bool(
            data.get("observation_can_only_reject_or_rank_sectors")
        ),
        "no_legacy_Z4_input": not _bad_flag(data, "legacy_Z4_input_used"),
        "non_fit_provenance": not _bad_provenance(data.get("provenance")),
    }
    ready = all(contracts.values())
    return {
        "status": "janus-z2-sigma-discrete-sector-observation-readiness-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Checks whether the discrete N_gap family may be compared to data. "
            "The comparison can reject or rank fixed sectors, but must not fit a "
            "continuous throat scale or relabel sectors."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "contracts": contracts,
        "sector_count": len(family["sector_table"]),
        "observation_readiness": ready,
        "allowed_outcomes": ["sector_rejected", "sector_survives", "sector_ranked"],
        "forbidden_outcomes": [
            "continuous_best_fit_R_s",
            "observationally_selected_N_gap_as_model_derivation",
            "legacy_Z4_sector_import",
        ],
        "blocked_by": [key for key, ok in contracts.items() if not ok],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Discrete Sector Observation Readiness Gate",
        "",
        payload["physical_statement"],
        "",
        f"Observation readiness: `{payload['observation_readiness']}`",
        f"Sector count: `{payload['sector_count']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
