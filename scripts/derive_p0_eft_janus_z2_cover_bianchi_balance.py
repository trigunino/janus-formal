from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_cover_bianchi import load_and_derive_bianchi_balances


INPUT_PATH = Path("outputs/active_z2_cover/projected_equations.json")
OUTPUT_PATH = Path("outputs/active_z2_cover/bianchi_balance.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_bianchi_balance.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_bianchi_balance.json")


def build_payload(input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-cover-bianchi-balance",
            "active_core": "JanusZ2CoverMasterAction",
            "input_path": str(input_path),
            "output_path": str(output_path),
            "input_manifest_present": False,
            "paired_bianchi_balance_ready": False,
            "paired_bianchi_closed": False,
            "full_no_fit_prediction_ready": False,
            "gate_passed": False,
            "primary_blocker": "projected_equations_missing",
        }
    payload = load_and_derive_bianchi_balances(input_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    payload.update(
        {
            "status": "janus-z2-cover-bianchi-balance",
            "input_path": str(input_path),
            "output_path": str(output_path),
            "input_manifest_present": True,
            "gate_passed": True,
        }
    )
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Cover Bianchi Balance",
        "",
        f"Input present: `{payload['input_manifest_present']}`",
        f"Balance ready: `{payload['paired_bianchi_balance_ready']}`",
        f"Bianchi closed: `{payload['paired_bianchi_closed']}`",
        f"Primary blocker: `{payload.get('primary_blocker', 'none')}`",
    ]
    if "balances" in payload:
        lines.extend(["", "## Balances"])
        lines.extend(f"- `{key}`: `{value}`" for key, value in payload["balances"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
