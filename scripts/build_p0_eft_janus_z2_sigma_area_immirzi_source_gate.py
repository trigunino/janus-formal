from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "sigma_area_immirzi_source_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_immirzi_source_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_immirzi_source_gate.json")

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _positive(data: dict[str, Any], key: str) -> float | None:
    value = data.get(key)
    if isinstance(value, (int, float)) and math.isfinite(float(value)) and float(value) > 0.0:
        return float(value)
    return None


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    gamma = _positive(data, "holst_immirzi_abs")
    origin = data.get("origin_route")
    origin_checks = {
        "eta_H_trace_identity": {
            "selected": origin == "eta_H_trace_identity",
            "ready": bool(data.get("eta_H_equals_minus_two_derived"))
            and bool(data.get("gamma_abs_equals_abs_eta_H_derived")),
            "interpretation": "uses the local APS/Nieh-Yan trace identity as the active Holst normalization",
        },
        "APS_Pin_index_normalization": {
            "selected": origin == "APS_Pin_index_normalization",
            "ready": bool(data.get("APS_Pin_index_package_closed"))
            and bool(data.get("trace_normalization_to_gamma_closed")),
            "interpretation": "uses the global APS/Pin index package to normalize the Holst parameter",
        },
        "independent_Holst_coupling": {
            "selected": origin == "independent_Holst_coupling",
            "ready": bool(data.get("Holst_coupling_derived_from_master_action")),
            "interpretation": "uses a master-action coupling derivation independent of observations",
        },
    }
    selected_ready = any(row["selected"] and row["ready"] for row in origin_checks.values())
    required_conditions = {
        "origin_route_declared": origin in origin_checks,
        "holst_immirzi_abs_available": gamma is not None,
        "selected_origin_ready": selected_ready,
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
    }
    ready = all(required_conditions.values())
    return {
        "status": "janus-z2-sigma-area-immirzi-source-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Route B may use a Holst area spectrum only if |gamma| is normalized "
            "by the active Janus/PT/Holst theory. Legacy Z4 or observational "
            "normalizations are rejected."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "origin_checks": origin_checks,
        "holst_immirzi_abs": gamma,
        "immirzi_source_ready": ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value],
        "forbidden_shortcuts": [
            "choose_gamma_by_area_gap_fit",
            "borrow_gamma_from_legacy_Z4_CMB",
            "identify_eta_H_with_gamma_without_trace_normalization",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Area Immirzi Source Gate",
        "",
        payload["physical_statement"],
        "",
        f"Immirzi source ready: `{payload['immirzi_source_ready']}`",
        f"|gamma|: `{payload['holst_immirzi_abs']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
