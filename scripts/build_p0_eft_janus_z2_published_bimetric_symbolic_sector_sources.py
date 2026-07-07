from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_published_bimetric_sector_ratio_gate import (
    build_payload as sector_ratio,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/published_bimetric_symbolic_sector_sources.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_bimetric_symbolic_sector_sources.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_bimetric_symbolic_sector_sources.json"
)


def build_payload(*, write_output: bool = False) -> dict:
    ratio = sector_ratio()
    r = ratio["ratio_payload"]["rho_minus0_over_rho_plus0"]
    source = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "published_bimetric_symbolic_sector_sources",
        "rho_plus0_symbol": "rho_plus0_abs",
        "rho_minus0_over_rho_plus0": r,
        "rho_minus0_symbol": f"({r})*rho_plus0_abs",
        "dust_shapes": {
            "rho_plus_of_a": "rho_plus0_abs * a_plus^-3",
            "rho_minus_of_a": f"({r}) * rho_plus0_abs * a_minus^-3",
        },
        "pressure_policy": {
            "dust_pressure_zero_symbolic": True,
            "generic_perfect_fluid_pressure_not_closed": True,
        },
        "absolute_density_scale_ready": False,
        "ready_for_numeric_sigma_pullback": False,
        "missing_input": "rho_plus0_abs from active global bimetric state",
    }
    if write_output:
        OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT_PATH.write_text(json.dumps(source, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-published-bimetric-symbolic-sector-sources",
        "active_core": "Z2_tunnel_Sigma",
        "symbolic_sector_sources_ready": True,
        "absolute_density_scale_ready": False,
        "ready_for_numeric_sigma_pullback": False,
        "source_manifest": source,
        "output_path": str(OUTPUT_PATH),
        "output_written": write_output,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Published Bimetric Symbolic Sector Sources",
        "",
        f"Symbolic sector sources ready: `{payload['symbolic_sector_sources_ready']}`",
        f"Absolute density scale ready: `{payload['absolute_density_scale_ready']}`",
        f"Missing input: `{payload['source_manifest']['missing_input']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
