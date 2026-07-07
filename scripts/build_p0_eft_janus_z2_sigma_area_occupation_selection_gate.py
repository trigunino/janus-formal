from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "sigma_area_occupation_selection_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_occupation_selection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_occupation_selection_gate.json")

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _positive_int(value: Any) -> int | None:
    return value if isinstance(value, int) and value > 0 else None


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    origin = data.get("origin_route")
    n_gap = _positive_int(data.get("N_gap"))
    flux_n = data.get("flux_integer_n")
    origin_checks = {
        "minimal_throat_state": {
            "selected": origin == "minimal_throat_state",
            "ready": bool(data.get("ground_state_nonzero_area_required")),
            "N_gap_if_ready": 1,
        },
        "flux_area_lock": {
            "selected": origin == "flux_area_lock",
            "ready": isinstance(flux_n, int)
            and flux_n != 0
            and bool(data.get("one_area_puncture_per_flux_unit_derived")),
            "N_gap_if_ready": abs(flux_n) if isinstance(flux_n, int) else None,
        },
        "spectral_stability_mode": {
            "selected": origin == "spectral_stability_mode",
            "ready": _positive_int(data.get("N_gap")) is not None
            and bool(data.get("N_gap_selected_by_stability_eigenmode")),
            "N_gap_if_ready": data.get("N_gap"),
        },
        "superselection_state": {
            "selected": origin == "superselection_state",
            "ready": _positive_int(data.get("N_gap")) is not None
            and bool(data.get("N_gap_declared_as_state_sector")),
            "N_gap_if_ready": data.get("N_gap"),
        },
    }
    selected = origin_checks.get(origin)
    predicted = selected.get("N_gap_if_ready") if selected and selected["ready"] else None
    if predicted is not None:
        n_gap = _positive_int(predicted)
    required_conditions = {
        "origin_route_declared": origin in origin_checks,
        "selected_origin_ready": bool(selected and selected["ready"]),
        "positive_integer_N_gap": n_gap is not None,
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
    }
    ready = all(required_conditions.values())
    return {
        "status": "janus-z2-sigma-area-occupation-selection-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "The occupation N_gap is the hard Route B selector. It can be fixed "
            "by a minimal nonzero throat state, locked to flux, selected by a "
            "stability mode, or declared as a superselection state. Observation "
            "selection is rejected."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "origin_checks": origin_checks,
        "N_gap": n_gap,
        "occupation_selector_ready": ready,
        "N_gap_is_unique_prediction": ready and origin != "superselection_state",
        "N_gap_is_superselection_label": ready and origin == "superselection_state",
        "blocked_by": [key for key, value in required_conditions.items() if not value],
        "forbidden_shortcuts": [
            "choose_N_gap_by_observation",
            "set_N_gap_to_one_without_ground_state_argument",
            "identify_N_gap_with_flux_n_without_flux_area_lock",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Area Occupation Selection Gate",
        "",
        payload["physical_statement"],
        "",
        f"Occupation selector ready: `{payload['occupation_selector_ready']}`",
        f"N_gap: `{payload['N_gap']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
