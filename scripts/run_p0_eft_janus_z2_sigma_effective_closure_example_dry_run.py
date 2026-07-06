from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.write_p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation import (
    build_payload as build_effective_closure_payload,
)


PARTIAL_PATH = Path(
    "outputs/active_z2_sigma/effective_partial_closure_from_projective_ratio.json"
)
EXAMPLE_OCCUPATION_PATH = Path(
    "outputs/examples/projected_occupation_state_inputs.example.json"
)
DIAGNOSTIC_OUTPUT_PATH = Path(
    "outputs/diagnostics/effective_closure_from_example_occupation.diagnostic.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_closure_example_dry_run.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_closure_example_dry_run.json"
)


def build_payload(
    *,
    partial_path: Path = PARTIAL_PATH,
    example_occupation_path: Path = EXAMPLE_OCCUPATION_PATH,
    diagnostic_output_path: Path = DIAGNOSTIC_OUTPUT_PATH,
) -> dict:
    closure = build_effective_closure_payload(
        partial_path=partial_path,
        occupation_path=example_occupation_path,
        output_path=diagnostic_output_path,
    )
    return {
        "status": "janus-z2-sigma-effective-closure-example-dry-run",
        "active_core": "Z2_tunnel_Sigma",
        "uses_non_active_example": True,
        "writes_active_manifest": False,
        "diagnostic_output_manifest": str(diagnostic_output_path),
        "diagnostic_effective_closure_ready": closure["effective_closure_ready"],
        "full_no_fit_prediction_ready": False,
        "active_effective_closure_path": "outputs/active_z2_sigma/effective_closure_inputs.json",
        "active_effective_closure_written": False,
        "example_N_occ_is_physical_derivation": False,
        "closure": closure,
        "gate_passed": closure["effective_closure_ready"],
        "primary_blocker": "none" if closure["effective_closure_ready"] else closure["primary_blocker"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective Closure Example Dry Run",
        "",
        f"Uses non-active example: `{payload['uses_non_active_example']}`",
        f"Writes active manifest: `{payload['writes_active_manifest']}`",
        f"Diagnostic closure ready: `{payload['diagnostic_effective_closure_ready']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        f"Example N_occ is physical derivation: `{payload['example_N_occ_is_physical_derivation']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
