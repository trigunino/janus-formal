from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_effective_closure_input_gate import (
    build_payload as build_effective_closure_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_bao_path_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_effective_bao_path_gate.json")


def build_payload() -> dict:
    closure = build_effective_closure_payload()
    closure_ready = bool(closure["effective_closure_ready"])
    required_after_closure = {
        "background_E_Z2Sigma": {
            "needed": True,
            "can_be_derived_from_two_effective_parameters_alone": False,
            "reason": "R_Sigma fixes a throat scale, not the full dimensionless expansion history E(z).",
        },
        "omega_k_Z2Sigma": {
            "needed": True,
            "can_be_derived_from_two_effective_parameters_alone": False,
            "reason": "needs a curvature convention relating R_Sigma to the FLRW spatial curvature scale.",
        },
        "c_s_over_c_Z2Sigma": {
            "needed": True,
            "can_be_derived_from_two_effective_parameters_alone": False,
            "reason": "needs photon temperature/radiation normalization plus baryon mass density.",
        },
        "Gamma_drag_over_H0_Z2Sigma": {
            "needed": True,
            "can_be_derived_from_two_effective_parameters_alone": False,
            "reason": "needs ionization/free-electron history, Thomson cross-section and H0 convention.",
        },
    }
    return {
        "status": "janus-z2-sigma-effective-bao-path-gate",
        "active_core": "Z2_tunnel_Sigma",
        "effective_closure_gate_passed": closure["gate_passed"],
        "effective_closure_ready": closure_ready,
        "effective_initial_data": closure["effective_initial_data"],
        "full_no_fit_prediction_ready": False,
        "effective_observational_closure": closure_ready,
        "two_parameter_closure_complete": closure_ready,
        "scale_free_BAO_ready_from_two_parameters_alone": False,
        "required_after_effective_closure": required_after_closure,
        "effective_scale_free_chi2_runner": (
            "scripts/build_p0_eft_janus_z2_sigma_effective_bao_scale_free_chi2_gate.py"
        ),
        "effective_scale_free_primitive_manifest": (
            "outputs/active_z2_sigma/effective_bao_scale_free_primitive_inputs.json"
        ),
        "gate_passed": closure_ready,
        "primary_blocker": "none" if closure_ready else closure["primary_blocker"],
        "next_required": [
            "derive or supply effective E_Z2Sigma(z) with provenance independent of Planck/LCDM/Z4",
            "derive or supply omega_k_Z2Sigma convention from R_Sigma_over_ell_collar_Z2Sigma",
            "derive or supply photon/baryon plasma normalization from N_Z2Sigma",
            "derive or supply ionization/Thomson drag history",
        ]
        if closure_ready
        else closure["next_required"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective BAO Path Gate",
        "",
        f"Effective closure ready: `{payload['effective_closure_ready']}`",
        f"Effective observational closure: `{payload['effective_observational_closure']}`",
        f"Scale-free BAO ready from two parameters alone: `{payload['scale_free_BAO_ready_from_two_parameters_alone']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
