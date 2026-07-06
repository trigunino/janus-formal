from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_cover_bianchi import attach_sigma_source_to_bianchi_balance


BALANCE_PATH = Path("outputs/active_z2_cover/bianchi_balance.json")
SIGMA_PATH = Path("outputs/active_z2_cover/sigma_source.json")
OUTPUT_PATH = Path("outputs/active_z2_cover/bianchi_balance_with_sigma_source.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_bianchi_with_sigma_source.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_cover_bianchi_with_sigma_source.json")


def build_payload(
    balance_path: Path = BALANCE_PATH,
    sigma_path: Path = SIGMA_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    missing = [str(path) for path in [balance_path, sigma_path] if not path.exists()]
    if missing:
        return {
            "status": "janus-z2-cover-bianchi-with-sigma-source",
            "active_core": "JanusZ2CoverMasterAction",
            "missing_inputs": missing,
            "sigma_source_attached": False,
            "paired_bianchi_closed": False,
            "gate_passed": False,
            "primary_blocker": "missing_bianchi_balance_or_sigma_source",
        }
    balance = json.loads(balance_path.read_text(encoding="utf-8"))
    sigma = json.loads(sigma_path.read_text(encoding="utf-8"))
    payload = attach_sigma_source_to_bianchi_balance(balance, sigma)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    payload.update(
        {
            "status": "janus-z2-cover-bianchi-with-sigma-source",
            "balance_path": str(balance_path),
            "sigma_path": str(sigma_path),
            "output_path": str(output_path),
            "gate_passed": True,
        }
    )
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Cover Bianchi With Sigma Source",
                "",
                f"Sigma source attached: `{payload['sigma_source_attached']}`",
                f"Bianchi closed: `{payload['paired_bianchi_closed']}`",
                f"Primary blocker: `{payload.get('primary_blocker', 'none')}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
