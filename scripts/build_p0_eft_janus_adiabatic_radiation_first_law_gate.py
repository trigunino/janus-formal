from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    adiabatic_radiation_first_law_derivation_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_adiabatic_radiation_first_law_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_adiabatic_radiation_first_law_gate.json")


def build_payload() -> dict:
    payload = adiabatic_radiation_first_law_derivation_payload()
    payload["gate_passed"] = payload["conditional_closure"]
    payload["promoted_as_unconditional"] = False
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Adiabatic Radiation First-Law Gate",
        "",
        f"Conditional closure: `{payload['conditional_closure']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Promoted as unconditional: `{payload['promoted_as_unconditional']}`",
        "",
        "## Conditional inputs",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["conditional_inputs"].items())
    lines.extend(["", "## Derived exponents"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["derived_exponents"].items())
    lines.extend(["", "## Remaining proof obligations"])
    lines.extend(f"- `{item}`" for item in payload["remaining_non_rustine_proof_obligations"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
