from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "flux_area_puncture_theorem_inputs.json"
OCCUPATION_OUTPUT_PATH = BASE / "sigma_area_occupation_selection_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flux_area_puncture_theorem_gate.md")

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _flux_integer(value: Any) -> int | None:
    return value if isinstance(value, int) and value != 0 else None


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    n_flux = _flux_integer(data.get("flux_integer_n"))
    required_conditions = {
        "active_core_Z2_tunnel_Sigma": data.get("active_core") == "Z2_tunnel_Sigma",
        "branch_null_PT_bridge": data.get("branch") == "Z2_null_Sigma_PT_bridge",
        "source_active_derived": data.get("source") == "active_derived",
        "flux_integer_n_available": n_flux is not None,
        "S2_throat_cycle_defined": bool(data.get("S2_throat_cycle_defined")),
        "global_U1_bundle_on_S2_throat": bool(data.get("global_U1_bundle_on_S2_throat")),
        "c1_flux_equals_n": bool(data.get("c1_flux_equals_n")),
        "U1_to_SU2_puncture_map_derived": bool(data.get("U1_to_SU2_puncture_map_derived")),
        "local_puncture_index_theorem_derived": bool(
            data.get("local_puncture_index_theorem_derived")
        ),
        "puncture_area_operator_coupled_to_flux_derived": bool(
            data.get("puncture_area_operator_coupled_to_flux_derived")
        ),
        "one_puncture_per_unit_flux_derived": bool(
            data.get("one_puncture_per_unit_flux_derived")
        ),
        "no_puncture_without_flux_derived": bool(data.get("no_puncture_without_flux_derived")),
        "unit_flux_puncture_irreducible": bool(data.get("unit_flux_puncture_irreducible")),
        "physical_induced_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
    }
    theorem_ready = all(required_conditions.values())
    n_gap = abs(n_flux) if theorem_ready and n_flux is not None else None
    return {
        "status": "janus-z2-sigma-flux-area-puncture-theorem-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "The flux-area lock N_gap=|n| is allowed only if the S2 throat U(1) "
            "Chern flux is mapped to SU(2)/spin area punctures by a derived local "
            "puncture theorem. Topological flux alone is insufficient."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "required_conditions": required_conditions,
        "puncture_theorem_ready": theorem_ready,
        "N_gap": n_gap,
        "occupation_payload": (
            {
                "origin_route": "flux_area_lock",
                "flux_integer_n": n_flux,
                "one_area_puncture_per_flux_unit_derived": True,
                "provenance": "active_flux_area_puncture_theorem",
            }
            if theorem_ready
            else None
        ),
        "blocked_by": [key for key, ok in required_conditions.items() if not ok],
        "forbidden_shortcuts": [
            "identify_Chern_flux_with_area_punctures_without_U1_to_SU2_map",
            "set_N_gap_equal_abs_n_from_topology_only",
            "choose_N_gap_by_observation",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(INPUT_PATH)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    if payload["occupation_payload"]:
        OCCUPATION_OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
        OCCUPATION_OUTPUT_PATH.write_text(
            json.dumps(payload["occupation_payload"], indent=2), encoding="utf-8"
        )
    lines = [
        "# Janus Z2 Sigma Flux-Area Puncture Theorem Gate",
        "",
        payload["physical_statement"],
        "",
        f"Puncture theorem ready: `{payload['puncture_theorem_ready']}`",
        f"N_gap: `{payload['N_gap']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
