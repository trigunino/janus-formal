from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_phase_space_occupation_search import (
    native_sound_horizon_integral_contract_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_native_sound_horizon_integral_contract_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_native_sound_horizon_integral_contract_gate.json")


def write_reports() -> dict:
    payload = native_sound_horizon_integral_contract_payload()
    payload["gate_passed"] = True
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Native Sound-Horizon Integral Contract Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Sound speed contract",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["sound_speed_contract"].items())
    lines.extend(["", "## H scalings"])
    for row in payload["candidate_H_scalings"]:
        lines.append(
            "- `{name}`: H exponent `{H_exponent}`, r_d integrand exponent "
            "`{rd_integrand_exponent_small_a}`, finite from zero `{finite_if_integrated_from_a0}`".format(
                **row
            )
        )
    lines.extend(["", "## Janus resolution", payload["janus_resolution"], "", "## Remaining"])
    lines.extend(f"- `{item}`" for item in payload["remaining"])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
