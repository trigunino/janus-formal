from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_acoustic_calculator_shape_phase_damping_gate import (
    build_payload as shape_payload,
)
from scripts.build_p0_eft_janus_z4_master_acoustic_calculator_component_spectra_gate import (
    build_payload as component_payload,
)
from scripts.build_p0_eft_janus_z4_master_lensing_remap_policy_gate import (
    build_payload as lensing_policy_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_solver_provenance_manifest_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_solver_provenance_manifest_gate.json")
MANIFEST_PATH = Path("outputs/reports/p0_eft_janus_z4_master_solver_provenance_manifest.json")


def _sha256(path: str | Path) -> str:
    p = Path(path)
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else "missing"


def build_payload() -> dict:
    shape = shape_payload()
    component = component_payload()
    lensing_policy = lensing_policy_payload()
    component_json = Path("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_component_spectra_gate.json")
    calculator_json = Path("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_payload.json")
    spectra_paths = [
        component["baseline_spectra_path"],
        *component["component_spectra_paths"].values(),
        lensing_policy["unlensed_spectra_path"],
        lensing_policy["lensed_spectra_path"],
        lensing_policy["lensing_kernel_path"],
    ]
    manifest = {
        "solver_name": "Janus Z4 CMB acoustic calculator",
        "solver_version": "solver-implementation-checkpoint-v1",
        "calculator_payload": str(calculator_json),
        "calculator_payload_hash": _sha256(calculator_json),
        "shape_gate_hash": _sha256("outputs/reports/p0_eft_janus_z4_master_acoustic_calculator_shape_phase_damping_gate.json"),
        "component_gate_hash": _sha256(component_json),
        "spectra_hashes": {path: _sha256(path) for path in spectra_paths},
        "source_component_channels": ["surface_SW", "early_ISW", "Doppler", "polarization_Pi"],
        "unlensed_spectra_path": lensing_policy["unlensed_spectra_path"],
        "lensed_spectra_path": lensing_policy["lensed_spectra_path"],
        "lensing_kernel_path": lensing_policy["lensing_kernel_path"],
        "lensing_remap_policy": lensing_policy["lensed_remap_policy"],
        "physical_lensing_solver": lensing_policy["physical_lensing_solver"],
        "unlensed_lensed_split_available": lensing_policy["unlensed_lensed_split_available"],
        "spectra_kind": "unlensed_and_lensed_total_diagnostic",
        "observed_likelihood_consumable": False,
        "cache_inputs": {
            "calculator_payload": str(calculator_json),
            "component_spectra_dir": "outputs/reports/z4_master_acoustic_calculator_component_spectra",
        },
    }
    MANIFEST_PATH.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return {
        "status": "janus-z4-master-solver-provenance-manifest-gate",
        "shape_phase_damping_gate_ready": shape["internal_shape_phase_damping_diagnostics_ready"],
        "manifest_path": str(MANIFEST_PATH),
        "manifest_hash": _sha256(MANIFEST_PATH),
        "cache_provenance_manifest_written": True,
        "component_spectra_hashes_recorded": bool(spectra_paths),
        "calculator_payload_hash_recorded": manifest["calculator_payload_hash"] != "missing",
        "unlensed_lensed_provenance_declared": True,
        "unlensed_lensed_split_available": lensing_policy["unlensed_lensed_split_available"],
        "spectra_kind": "unlensed_and_lensed_total_diagnostic",
        "lensing_remap_policy": lensing_policy["lensed_remap_policy"],
        "physical_lensing_solver": lensing_policy["physical_lensing_solver"],
        "observed_likelihood_allowed": False,
        "planck_retry_allowed": False,
        "candidate_promotion_allowed": False,
        "retuning_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterSolverImplementationReadinessGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Solver Provenance Manifest Gate",
        "",
        f"Manifest written: `{payload['cache_provenance_manifest_written']}`",
        f"Manifest hash: `{payload['manifest_hash']}`",
        f"Spectra kind: `{payload['spectra_kind']}`",
        f"Planck retry allowed: `{payload['planck_retry_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
