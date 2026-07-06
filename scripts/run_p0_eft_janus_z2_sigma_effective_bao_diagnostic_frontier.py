from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_effective_bao_end_to_end_gate import (
    build_payload as build_end_to_end_payload,
)


DIAGNOSTIC_CLOSURE_PATH = Path(
    "outputs/diagnostics/effective_closure_from_example_occupation.diagnostic.json"
)
DIAGNOSTIC_PRIMITIVE_PATH = Path(
    "outputs/diagnostics/effective_bao_scale_free_primitive_inputs.diagnostic.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_diagnostic_frontier.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_diagnostic_frontier.json"
)


def build_payload(
    *,
    closure_path: Path = DIAGNOSTIC_CLOSURE_PATH,
    primitive_path: Path = DIAGNOSTIC_PRIMITIVE_PATH,
) -> dict:
    end_to_end = build_end_to_end_payload(
        closure_input_path=closure_path,
        primitive_input_path=primitive_path,
    )
    primitives_available = bool(end_to_end["effective_primitive_manifest_available"])
    return {
        "status": "janus-z2-sigma-effective-bao-diagnostic-frontier",
        "active_core": "Z2_tunnel_Sigma",
        "uses_diagnostic_closure": True,
        "writes_active_manifest": False,
        "closure_path": str(closure_path),
        "primitive_path": str(primitive_path),
        "effective_closure_ready": end_to_end["effective_closure_ready"],
        "effective_primitive_manifest_available": end_to_end[
            "effective_primitive_manifest_available"
        ],
        "effective_bao_chi2_evaluated": end_to_end["effective_bao_chi2_evaluated"],
        "chi2_DESI_DR2_BAO_effective_diagnostic": end_to_end.get(
            "chi2_DESI_DR2_BAO_effective"
        ),
        "z_d_Z2Sigma_effective_diagnostic": end_to_end.get("z_d_Z2Sigma_effective"),
        "rhat_d_Z2Sigma_effective_diagnostic": end_to_end.get(
            "rhat_d_Z2Sigma_effective"
        ),
        "full_no_fit_prediction_ready": False,
        "missing_effective_primitives": []
        if primitives_available
        else [
            "E_Z2Sigma(z)",
            "c_s_over_c_Z2Sigma(z)",
            "Gamma_drag_over_H0_Z2Sigma(z)",
            "omega_k_Z2Sigma",
        ],
        "diagnostic_primitives_are_physical_derivation": False,
        "gate_passed": False,
        "primary_blocker": "diagnostic_only_not_physical_primitives"
        if primitives_available
        else "effective_bao_scale_free_primitive_inputs",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective BAO Diagnostic Frontier",
        "",
        f"Uses diagnostic closure: `{payload['uses_diagnostic_closure']}`",
        f"Effective closure ready: `{payload['effective_closure_ready']}`",
        f"Primitive manifest available: `{payload['effective_primitive_manifest_available']}`",
        f"BAO chi2 evaluated: `{payload['effective_bao_chi2_evaluated']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        f"Diagnostic DESI DR2 BAO chi2: `{payload['chi2_DESI_DR2_BAO_effective_diagnostic']}`",
        f"Diagnostic z_d: `{payload['z_d_Z2Sigma_effective_diagnostic']}`",
        f"Diagnostic rhat_d: `{payload['rhat_d_Z2Sigma_effective_diagnostic']}`",
        "",
        "## Missing Effective Primitives",
    ]
    lines.extend(f"- `{item}`" for item in payload["missing_effective_primitives"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
