from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_physical_inputs_to_scale_free_bao_chi2_gate import (
    build_payload as build_physical_bao_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_real_state_materialization_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_real_state_materialization_gate.json")


def _missing_from_frontier(payload: dict) -> list[str]:
    frontier = payload.get("nearest_physical_inputs_frontier", {})
    blocks = frontier.get("blocks", [])
    return [str(item) for item in blocks]


def build_payload(*, physical_payload: dict | None = None) -> dict:
    physical = physical_payload if physical_payload is not None else build_physical_bao_payload()
    missing = _missing_from_frontier(physical)
    evaluated = bool(physical.get("bao_chi2_evaluated"))
    gate_passed = bool(physical.get("gate_passed"))
    real_state_ready = evaluated and gate_passed and not missing
    return {
        "status": "janus-z2-sigma-bao-real-state-materialization-gate",
        "active_core": "Z2_tunnel_Sigma",
        "physical_inputs_gate": physical.get("status"),
        "physical_inputs_gate_passed": gate_passed,
        "bao_chi2_evaluated": evaluated,
        "chi2_DESI_DR2_BAO": physical.get("chi2_DESI_DR2_BAO"),
        "prediction_vector_length": len(physical.get("prediction_vector") or []),
        "missing_real_active_inputs": missing,
        "real_active_inputs_missing": bool(missing) or not evaluated,
        "pipeline_evaluable_with_strict_inputs": True,
        "fixture_result_is_not_physical_result": not real_state_ready,
        "uses_compressed_planck_lcdm": bool(physical.get("uses_compressed_planck_lcdm")),
        "uses_archived_z4": bool(physical.get("uses_archived_z4")),
        "uses_observational_H0_fit": bool(physical.get("uses_observational_H0_fit")),
        "uses_observational_curvature_fit": bool(physical.get("uses_observational_curvature_fit")),
        "gate_passed": real_state_ready,
        "blocker": None
        if real_state_ready
        else physical.get("blocker") or "real active BAO input manifests are incomplete",
        "next_required": []
        if real_state_ready
        else [
            "materialize_active_FLRW_component_manifest",
            "derive_active_H0_Z2Sigma_and_R_curv_Z2Sigma_separately",
            "materialize_projected_baryon_number_charge_Z2Sigma",
            "materialize_early_plasma_manifest",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Real-State Materialization Gate",
        "",
        f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
        f"Real active inputs missing: `{payload['real_active_inputs_missing']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Fixture result is not physical result: `{payload['fixture_result_is_not_physical_result']}`",
    ]
    if payload["chi2_DESI_DR2_BAO"] is not None:
        lines.append(f"DESI DR2 BAO chi2: `{payload['chi2_DESI_DR2_BAO']}`")
    if payload["missing_real_active_inputs"]:
        lines.extend(["", "## Missing Real Active Inputs"])
        lines.extend(f"- `{item}`" for item in payload["missing_real_active_inputs"])
    if payload["blocker"]:
        lines.extend(["", "## Blocker", payload["blocker"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
