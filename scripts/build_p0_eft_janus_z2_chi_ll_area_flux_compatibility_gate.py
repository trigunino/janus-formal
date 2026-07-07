from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_chi_ll_area_gap_exit_gate import (
    INPUT_PATH as AREA_INPUT_PATH,
    build_payload as build_area_gap,
)
from scripts.build_p0_eft_janus_z2_null_sigma_chi_ll_superselection_flux_reducer_gate import (
    INPUT_PATH as FLUX_INPUT_PATH,
    build_payload as build_flux,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_area_flux_compatibility_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_chi_ll_area_flux_compatibility_gate.json")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    *,
    area_input_path: Path = AREA_INPUT_PATH,
    flux_input_path: Path = FLUX_INPUT_PATH,
) -> dict[str, Any]:
    area = build_area_gap(area_input_path)
    flux = build_flux(input_path=flux_input_path)
    area_data = _read(area_input_path)
    flux_data = _read(flux_input_path)
    compatibility = None
    if area["area_gap_exit_ready"] and flux["gate_passed"]:
        area_radius = area["derivation"]["R_s_m"]
        flux_radius = flux["computed"]["R_s_m"]
        rel = abs(area_radius - flux_radius) / max(area_radius, flux_radius)
        compatibility = {
            "area_R_s_m": area_radius,
            "flux_R_s_m": flux_radius,
            "relative_difference": rel,
            "compatible": rel < 1.0e-12,
        }
    required_conditions = {
        "area_gap_manifest_ready": area["area_gap_exit_ready"],
        "flux_superselection_manifest_ready": flux["gate_passed"],
        "shared_physical_area_gauge": (
            area_data.get("area_gauge") == "physical_induced_S2_metric"
            and flux_data.get("area_gauge") == "physical_induced_S2_metric"
        ),
        "non_observational_area_provenance": bool(area_data.get("non_observational_provenance")),
        "non_observational_flux_provenance": flux["gate_passed"],
    }
    ready = all(required_conditions.values()) and bool(
        compatibility and compatibility["compatible"]
    )
    return {
        "status": "janus-z2-chi-ll-area-flux-compatibility-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Area-gap and S2 flux quantization can jointly select the throat only "
            "if they agree on the same physical induced area: "
            "N_gap*A_gap = 4*pi*R_s(flux)^2."
        ),
        "required_conditions": required_conditions,
        "compatibility": compatibility,
        "formulae": {
            "area_gap": "A_Sigma=N_gap*A_gap",
            "flux_radius": "R_s=(2*(n/(2*q_LL))^2/F2_0)^(1/4)",
            "compatibility": "N_gap*A_gap = 4*pi*R_s(flux)^2",
        },
        "area_input_path": str(area_input_path),
        "flux_input_path": str(flux_input_path),
        "area_flux_compatibility_ready": ready,
        "chi_LL_prediction_ready": ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + ([] if compatibility else ["area_or_flux_radius_missing"])
        + ([] if not compatibility or compatibility["compatible"] else ["area_flux_radius_mismatch"]),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Area-Flux Compatibility Gate",
        "",
        payload["physical_statement"],
        "",
        f"Compatibility ready: `{payload['area_flux_compatibility_ready']}`",
        f"chi_LL prediction ready: `{payload['chi_LL_prediction_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
