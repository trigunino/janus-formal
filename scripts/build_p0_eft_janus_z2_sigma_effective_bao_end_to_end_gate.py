from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_effective_bao_scale_free_chi2_gate import (
    INPUT_PATH as PRIMITIVE_INPUT_PATH,
    build_payload as build_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_effective_closure_input_gate import (
    INPUT_PATH as CLOSURE_INPUT_PATH,
    build_payload as build_closure_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_bao_end_to_end_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_bao_end_to_end_gate.json")


def build_payload(
    *,
    closure_input_path: Path = CLOSURE_INPUT_PATH,
    primitive_input_path: Path = PRIMITIVE_INPUT_PATH,
) -> dict:
    closure = build_closure_payload(input_path=closure_input_path)
    chi2 = build_chi2_payload(input_path=primitive_input_path)
    end_to_end_ready = bool(
        closure["gate_passed"]
        and chi2["gate_passed"]
        and chi2.get("effective_bao_chi2_evaluated", False)
    )
    if not closure["gate_passed"]:
        blocker = closure["primary_blocker"]
    elif not chi2["gate_passed"]:
        blocker = chi2["blocker"]
    else:
        blocker = "none"
    return {
        "status": "janus-z2-sigma-effective-bao-end-to-end-gate",
        "active_core": "Z2_tunnel_Sigma",
        "closure_input_manifest": str(closure_input_path),
        "primitive_input_manifest": str(primitive_input_path),
        "effective_closure_ready": closure["effective_closure_ready"],
        "effective_primitive_manifest_available": chi2[
            "effective_primitive_manifest_available"
        ],
        "effective_bao_chi2_evaluated": chi2["effective_bao_chi2_evaluated"],
        "effective_bao_end_to_end_ready": end_to_end_ready,
        "full_no_fit_prediction_ready": False,
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_fit": False,
        "chi2_DESI_DR2_BAO_effective": chi2.get("chi2_DESI_DR2_BAO_effective"),
        "z_d_Z2Sigma_effective": chi2.get("z_d_Z2Sigma_effective"),
        "rhat_d_Z2Sigma_effective": chi2.get("rhat_d_Z2Sigma_effective"),
        "prediction_vector_length": chi2.get("prediction_vector_length"),
        "residual_vector_length": chi2.get("residual_vector_length"),
        "gate_passed": end_to_end_ready,
        "primary_blocker": blocker,
        "next_required": []
        if end_to_end_ready
        else [
            "provide valid effective_closure_inputs.json",
            "provide valid effective_bao_scale_free_primitive_inputs.json",
            "ensure primitive manifest hashes the effective closure manifest",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective BAO End-To-End Gate",
        "",
        f"Effective closure ready: `{payload['effective_closure_ready']}`",
        f"Primitive manifest available: `{payload['effective_primitive_manifest_available']}`",
        f"Effective BAO chi2 evaluated: `{payload['effective_bao_chi2_evaluated']}`",
        f"End-to-end ready: `{payload['effective_bao_end_to_end_ready']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
    ]
    if payload["chi2_DESI_DR2_BAO_effective"] is not None:
        lines.append(f"DESI DR2 BAO effective chi2: `{payload['chi2_DESI_DR2_BAO_effective']}`")
    if payload["primary_blocker"] != "none":
        lines.append(f"Blocker: `{payload['primary_blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
