from __future__ import annotations

import hashlib
import json
from pathlib import Path

from janus_lab.data import load_desi_bao
from janus_lab.z2_sigma_active_inputs import load_active_z2sigma_bao_inputs
from janus_lab.z2_sigma_bao import chi2_against_desi


INPUT_PATH = Path("outputs/active_z2_sigma/bao_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_official_chi2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_official_chi2_gate.json")


def build_payload(input_path: Path = INPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-bao-official-chi2-gate",
            "active_core": "Z2_tunnel_Sigma",
            "input_manifest": str(input_path),
            "active_manifest_available": False,
            "official_bao_evaluation": False,
            "bao_chi2_evaluated": False,
            "bao_official_chi2_gate_passed": False,
            "blocker": "missing active-derived BAO input manifest",
        }

    inputs = load_active_z2sigma_bao_inputs(input_path)
    manifest = json.loads(input_path.read_text(encoding="utf-8"))
    source_component_manifest_path = Path(manifest["source_component_manifest_path"])
    source_component_manifest_available = source_component_manifest_path.exists()
    source_hash_matches_manifest = False
    if source_component_manifest_available:
        source_hash_matches_manifest = (
            hashlib.sha256(source_component_manifest_path.read_bytes()).hexdigest()
            == manifest["source_component_manifest_sha256"]
        )
    rd = inputs.rd_mpc()
    dataset = load_desi_bao()
    result = chi2_against_desi(
        dataset,
        inputs.h_z2sigma,
        rd,
        omega_k_z2sigma=inputs.omega_k_z2sigma,
    )
    return {
        "status": "janus-z2-sigma-bao-official-chi2-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "input_provenance": manifest["input_provenance"],
        "source_component_manifest_path": manifest["source_component_manifest_path"],
        "source_component_manifest_sha256": manifest["source_component_manifest_sha256"],
        "source_component_manifest_available": source_component_manifest_available,
        "source_hash_matches_manifest": source_hash_matches_manifest,
        "active_manifest_available": True,
        "official_bao_evaluation": True,
        "bao_chi2_evaluated": True,
        "data_points": int(dataset.value.size),
        "prediction_vector": result.prediction.tolist(),
        "residual_vector": result.residual.tolist(),
        "rd_Z2Sigma_mpc": float(rd),
        "omega_k_Z2Sigma": float(inputs.omega_k_z2sigma),
        "chi2_DESI_DR2_BAO": float(result.chi2),
        "bao_official_chi2_gate_passed": source_hash_matches_manifest,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Official Chi2 Gate",
        "",
        f"Input manifest: `{payload['input_manifest']}`",
        f"Active manifest available: `{payload['active_manifest_available']}`",
        f"Official BAO evaluation: `{payload['official_bao_evaluation']}`",
        f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
        f"Gate passed: `{payload['bao_official_chi2_gate_passed']}`",
    ]
    if payload.get("bao_chi2_evaluated"):
        lines.append(f"Source component manifest: `{payload['source_component_manifest_path']}`")
        lines.append(f"Source hash verified: `{payload['source_hash_matches_manifest']}`")
        lines.append(f"DESI DR2 BAO chi2: `{payload['chi2_DESI_DR2_BAO']}`")
    else:
        lines.append(f"Blocker: `{payload['blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
