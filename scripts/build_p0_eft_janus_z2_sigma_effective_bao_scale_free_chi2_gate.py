from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.data import load_desi_bao
from janus_lab.z2_sigma_bao import chi2_against_desi_scale_free, dimensionless_sound_ruler
from janus_lab.z2_sigma_early_plasma import (
    find_drag_epoch_bracket_z2sigma,
    solve_drag_epoch_z2sigma,
)
from janus_lab.z2_sigma_effective_bao import load_effective_scale_free_primitive_inputs


INPUT_PATH = Path("outputs/active_z2_sigma/effective_bao_scale_free_primitive_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_scale_free_chi2_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_bao_scale_free_chi2_gate.json"
)


def _sample(z_grid, values) -> list[dict[str, float]]:
    last = len(z_grid) - 1
    indices = sorted({0, last // 2, last})
    return [{"z": float(z_grid[index]), "value": float(values[index])} for index in indices]


def build_payload(input_path: Path = INPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-effective-bao-scale-free-chi2-gate",
            "active_core": "Z2_tunnel_Sigma",
            "input_manifest": str(input_path),
            "effective_primitive_manifest_available": False,
            "effective_bao_chi2_evaluated": False,
            "full_no_fit_prediction_ready": False,
            "gate_passed": False,
            "blocker": "missing effective scale-free primitive input manifest",
        }
    manifest = json.loads(input_path.read_text(encoding="utf-8"))
    primitives = load_effective_scale_free_primitive_inputs(input_path)
    closure_path = Path(manifest["source_effective_closure_path"])
    closure_available = closure_path.exists()
    closure_hash_matches = False
    if closure_available:
        closure_hash_matches = (
            hashlib.sha256(closure_path.read_bytes()).hexdigest()
            == manifest["source_effective_closure_sha256"]
        )
    if primitives.z_d_bracket is None:
        positive_grid = primitives.z_grid[primitives.z_grid > 0.0]
        z_low, z_high = find_drag_epoch_bracket_z2sigma(
            primitives.e_z2sigma,
            primitives.gamma_drag_over_h0_z2sigma,
            positive_grid,
        )
    else:
        z_low, z_high = primitives.z_d_bracket
    z_d = solve_drag_epoch_z2sigma(
        primitives.e_z2sigma,
        primitives.gamma_drag_over_h0_z2sigma,
        z_low=z_low,
        z_high=z_high,
    )
    rd_hat = dimensionless_sound_ruler(
        primitives.e_z2sigma,
        primitives.cs_over_c_z2sigma,
        z_d,
        z_max=primitives.z_max,
        samples=min(max(len(primitives.z_grid), 64), 8192),
    )
    dataset = load_desi_bao()
    result = chi2_against_desi_scale_free(
        dataset,
        primitives.e_z2sigma,
        rd_hat,
        omega_k_z2sigma=primitives.omega_k_z2sigma,
    )
    return {
        "status": "janus-z2-sigma-effective-bao-scale-free-chi2-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "effective_primitive_manifest_available": True,
        "source_effective_closure_path": manifest["source_effective_closure_path"],
        "source_effective_closure_available": closure_available,
        "source_effective_closure_hash_matches": closure_hash_matches,
        "effective_bao_chi2_evaluated": True,
        "full_no_fit_prediction_ready": False,
        "effective_observational_closure": True,
        "data_points": int(dataset.value.size),
        "z_d_Z2Sigma_effective": float(z_d),
        "rhat_d_Z2Sigma_effective": float(rd_hat),
        "omega_k_Z2Sigma_effective": float(primitives.omega_k_z2sigma),
        "E_Z2Sigma_sample": _sample(primitives.z_grid, primitives.e_grid),
        "c_s_over_c_Z2Sigma_sample": _sample(primitives.z_grid, primitives.cs_over_c_grid),
        "Gamma_drag_over_H0_Z2Sigma_sample": _sample(
            primitives.z_grid, primitives.gamma_drag_over_h0_grid
        ),
        "prediction_vector": result.prediction.tolist(),
        "residual_vector": result.residual.tolist(),
        "prediction_vector_length": int(result.prediction.size),
        "residual_vector_length": int(result.residual.size),
        "chi2_DESI_DR2_BAO_effective": float(result.chi2),
        "gate_passed": closure_hash_matches,
        "blocker": "none" if closure_hash_matches else "source_effective_closure_hash",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective BAO Scale-Free Chi2 Gate",
        "",
        f"Effective primitive manifest available: `{payload['effective_primitive_manifest_available']}`",
        f"Effective BAO chi2 evaluated: `{payload['effective_bao_chi2_evaluated']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload.get("effective_bao_chi2_evaluated"):
        lines.append(f"DESI DR2 BAO effective chi2: `{payload['chi2_DESI_DR2_BAO_effective']}`")
        lines.append(f"z_d effective: `{payload['z_d_Z2Sigma_effective']}`")
        lines.append(f"rhat_d effective: `{payload['rhat_d_Z2Sigma_effective']}`")
    else:
        lines.append(f"Blocker: `{payload['blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
