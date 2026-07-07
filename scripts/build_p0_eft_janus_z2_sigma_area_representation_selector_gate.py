from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "sigma_area_representation_selector_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_representation_selector_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_representation_selector_gate.json")

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _valid_spin(value: Any) -> float | None:
    if not isinstance(value, (int, float)) or float(value) <= 0:
        return None
    doubled = 2.0 * float(value)
    if abs(doubled - round(doubled)) > 1.0e-12:
        return None
    return float(value)


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    j_min = _valid_spin(data.get("j_min"))
    origin = data.get("origin_route")
    origin_checks = {
        "minimal_nontrivial_SU2": {
            "selected": origin == "minimal_nontrivial_SU2",
            "ready": bool(data.get("Sigma_area_carried_by_SU2_flux"))
            and bool(data.get("trivial_j0_excluded_by_nonzero_throat_area")),
            "j_min_if_ready": 0.5,
        },
        "Pin_spin_boundary_mode": {
            "selected": origin == "Pin_spin_boundary_mode",
            "ready": bool(data.get("Pin_spinor_boundary_mode_derived"))
            and bool(data.get("spin_representation_projected_to_Sigma")),
            "j_min_if_ready": data.get("j_min"),
        },
        "state_sector_representation": {
            "selected": origin == "state_sector_representation",
            "ready": bool(data.get("representation_selected_by_state_sector")),
            "j_min_if_ready": data.get("j_min"),
        },
    }
    selected = origin_checks.get(origin)
    predicted = selected.get("j_min_if_ready") if selected and selected["ready"] else None
    if predicted is not None:
        j_min = _valid_spin(predicted)
    required_conditions = {
        "origin_route_declared": origin in origin_checks,
        "selected_origin_ready": bool(selected and selected["ready"]),
        "valid_half_integer_j_min": j_min is not None,
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
    }
    ready = all(required_conditions.values())
    return {
        "status": "janus-z2-sigma-area-representation-selector-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "The area spectrum needs a representation selector. The default "
            "minimal nontrivial SU(2) route gives j_min=1/2 only after the "
            "Sigma throat carries nonzero SU(2) flux and j=0 is excluded."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "origin_checks": origin_checks,
        "j_min": j_min,
        "representation_selector_ready": ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value],
        "forbidden_shortcuts": [
            "choose_j_min_by_observation",
            "assume_j_min_half_without_nonzero_flux_or_state_argument",
            "reuse_legacy_Z4_representation",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Area Representation Selector Gate",
        "",
        payload["physical_statement"],
        "",
        f"Representation selector ready: `{payload['representation_selector_ready']}`",
        f"j_min: `{payload['j_min']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
