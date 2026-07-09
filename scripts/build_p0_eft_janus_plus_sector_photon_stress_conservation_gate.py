from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    plus_sector_photon_stress_conservation_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_plus_sector_photon_stress_conservation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_plus_sector_photon_stress_conservation_gate.json")


def build_payload() -> dict:
    payload = plus_sector_photon_stress_conservation_payload()
    payload["gate_passed"] = payload[
        "plus_sector_photon_stress_conservation_conditionally_derived"
    ]
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Plus-Sector Photon Stress-Conservation Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        "Unconditional closure within extension: "
        f"`{payload['plus_sector_photon_stress_conservation_unconditionally_derived_within_extension']}`",
        "Paper-native closure: "
        f"`{payload['plus_sector_photon_stress_conservation_paper_native']}`",
        "Radiation first law unblocked within extension: "
        f"`{payload['radiation_first_law_unblocked_within_extension']}`",
        "",
        "## Anchors",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["anchors"].items())
    lines.extend(["", "## Required action inputs"])
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in payload["required_action_inputs"].items()
    )
    lines.extend(["", "## Conditional Noether derivation"])
    lines.extend(
        f"- `{key}`: `{value}`"
        for key, value in payload["conditional_noether_derivation"].items()
    )
    lines.extend(["", "## Remaining proof obligations"])
    lines.extend(f"- `{item}`" for item in payload["remaining_non_rustine_proof_obligations"])
    lines.extend(["", "## Bottom line", payload["bottom_line"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
