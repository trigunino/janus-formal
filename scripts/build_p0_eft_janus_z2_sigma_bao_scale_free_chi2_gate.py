from __future__ import annotations

import hashlib
import json
from pathlib import Path

from janus_lab.data import load_desi_bao
from janus_lab.z2_sigma_active_inputs import load_active_z2sigma_scale_free_bao_inputs
from janus_lab.z2_sigma_bao import chi2_against_desi_scale_free


INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_chi2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_scale_free_chi2_gate.json")


def _grid_sample(z_grid, values) -> list[dict[str, float]]:
    last = len(z_grid) - 1
    indices = sorted({0, last // 2, last})
    return [
        {"z": float(z_grid[index]), "value": float(values[index])}
        for index in indices
    ]


def build_payload(input_path: Path = INPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-bao-scale-free-chi2-gate",
            "active_core": "Z2_tunnel_Sigma",
            "input_manifest": str(input_path),
            "active_manifest_available": False,
            "scale_free_bao_evaluation": False,
            "bao_chi2_evaluated": False,
            "bao_scale_free_chi2_gate_passed": False,
            "blocker": "missing active-derived scale-free BAO input manifest",
        }

    inputs = load_active_z2sigma_scale_free_bao_inputs(input_path)
    manifest = json.loads(input_path.read_text(encoding="utf-8"))
    source_component_manifest_path = Path(manifest["source_component_manifest_path"])
    source_component_manifest_available = source_component_manifest_path.exists()
    source_hash_matches_manifest = False
    if source_component_manifest_available:
        source_hash_matches_manifest = (
            hashlib.sha256(source_component_manifest_path.read_bytes()).hexdigest()
            == manifest["source_component_manifest_sha256"]
        )
    rd_hat = inputs.rd_hat()
    gamma_grid = inputs.gamma_drag_over_h0_grid
    gamma_available = gamma_grid is not None
    dataset = load_desi_bao()
    result = chi2_against_desi_scale_free(
        dataset,
        inputs.e_z2sigma,
        rd_hat,
        omega_k_z2sigma=inputs.omega_k_z2sigma,
    )
    return {
        "status": "janus-z2-sigma-bao-scale-free-chi2-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "input_provenance": manifest["input_provenance"],
        "source_component_manifest_path": manifest["source_component_manifest_path"],
        "source_component_manifest_sha256": manifest["source_component_manifest_sha256"],
        "source_component_manifest_available": source_component_manifest_available,
        "source_hash_matches_manifest": source_hash_matches_manifest,
        "active_manifest_available": True,
        "scale_free_bao_evaluation": True,
        "official_dimensional_bao_gate_unblocked": False,
        "bao_chi2_evaluated": True,
        "data_points": int(dataset.value.size),
        "prediction_vector": result.prediction.tolist(),
        "residual_vector": result.residual.tolist(),
        "prediction_vector_length": int(result.prediction.size),
        "residual_vector_length": int(result.residual.size),
        "rd_hat_Z2Sigma": float(rd_hat),
        "omega_k_Z2Sigma": float(inputs.omega_k_z2sigma),
        "E_Z2Sigma_sample": _grid_sample(inputs.z_grid, inputs.e_grid),
        "c_s_over_c_Z2Sigma_sample": _grid_sample(inputs.z_grid, inputs.cs_over_c_grid),
        "Gamma_drag_over_H0_Z2Sigma_available": gamma_available,
        "Gamma_drag_over_H0_Z2Sigma_sample": (
            _grid_sample(inputs.z_grid, gamma_grid) if gamma_available else []
        ),
        "chi2_DESI_DR2_BAO": float(result.chi2),
        "bao_scale_free_chi2_gate_passed": source_hash_matches_manifest,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Scale-Free Chi2 Gate",
        "",
        f"Input manifest: `{payload['input_manifest']}`",
        f"Active manifest available: `{payload['active_manifest_available']}`",
        f"Scale-free BAO evaluation: `{payload['scale_free_bao_evaluation']}`",
        f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
        f"Gate passed: `{payload['bao_scale_free_chi2_gate_passed']}`",
    ]
    if payload.get("bao_chi2_evaluated"):
        lines.append(f"Source component manifest: `{payload['source_component_manifest_path']}`")
        lines.append(f"Source hash verified: `{payload['source_hash_matches_manifest']}`")
        lines.append(
            f"Gamma_drag/H0 available: `{payload['Gamma_drag_over_H0_Z2Sigma_available']}`"
        )
        lines.append(f"Prediction vector length: `{payload['prediction_vector_length']}`")
        lines.append(f"DESI DR2 BAO chi2: `{payload['chi2_DESI_DR2_BAO']}`")
    else:
        lines.append(f"Blocker: `{payload['blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
