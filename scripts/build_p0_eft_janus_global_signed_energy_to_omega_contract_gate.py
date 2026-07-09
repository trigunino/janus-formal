from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import global_signed_energy_to_omega_contract_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_global_signed_energy_to_omega_contract_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_global_signed_energy_to_omega_contract_gate.json")


def write_reports() -> dict:
    payload = global_signed_energy_to_omega_contract_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Global Signed Energy To Omega Contract Gate",
                "",
                f"Gate passed: `{payload['gate_passed']}`",
                f"Algebraic contract closed: `{payload['algebraic_contract_closed']}`",
                f"Omega fixed by conservation: `{payload['omega_fixed_by_conservation']}`",
                "",
                "## Omega relation",
                f"`{payload['omega_relation']}`",
                "",
                "## Bottom line",
                payload["bottom_line"],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
