from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


INPUT_PATH = Path("outputs/active_z2_sigma/coframe_connection_pullback_components_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/torsion_pullback_components_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_torsion_pullback_components_from_coframe_connection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_torsion_pullback_components_from_coframe_connection_gate.json")


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("coframe/connection active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("coframe/connection source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    for key in [
        "coframe_pullback_ready",
        "spin_connection_pullback_ready",
        "exterior_derivative_coframe_ready",
    ]:
        if payload.get(key) is not True:
            raise ValueError(f"{key} must be true")
    if payload.get("selected_route") != "cartan_first_structure_equation":
        raise ValueError("selected_route must be cartan_first_structure_equation")
    return payload


def _cartan_torsion(q_ab, coframe_e_I_a, exterior_de_I_ab, spin_connection_omega_IJ_a) -> dict:
    q = np.asarray(q_ab, dtype=float)
    e = np.asarray(coframe_e_I_a, dtype=float)
    de = np.asarray(exterior_de_I_ab, dtype=float)
    omega = np.asarray(spin_connection_omega_IJ_a, dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1]:
        raise ValueError("q_ab must be square")
    n = q.shape[0]
    if not np.allclose(q, q.T, atol=1e-10):
        raise ValueError("q_ab must be symmetric")
    if abs(float(np.linalg.det(q))) < 1e-14:
        raise ValueError("q_ab must be nondegenerate")
    if e.shape != (n, n):
        raise ValueError("coframe_e_I_a must have shape n x n")
    if de.shape != (n, n, n):
        raise ValueError("exterior_de_I_ab must have shape n x n x n")
    if omega.shape != (n, n, n):
        raise ValueError("spin_connection_omega_IJ_a must have shape n x n x n")
    if not np.all(np.isfinite(q)) or not np.all(np.isfinite(e)) or not np.all(np.isfinite(de)) or not np.all(np.isfinite(omega)):
        raise ValueError("all coframe/connection arrays must be finite")
    if abs(float(np.linalg.det(e))) < 1e-14:
        raise ValueError("coframe_e_I_a must be invertible")
    if not np.allclose(de + np.swapaxes(de, 1, 2), 0.0, atol=1e-8):
        raise ValueError("exterior_de_I_ab must be antisymmetric in a,b")
    if not np.allclose(omega + np.swapaxes(omega, 0, 1), 0.0, atol=1e-8):
        raise ValueError("spin_connection_omega_IJ_a must be antisymmetric in I,J")

    torsion_internal = np.zeros((n, n, n), dtype=float)
    for i in range(n):
        for a in range(n):
            for b in range(n):
                torsion_internal[i, a, b] = de[i, a, b] + sum(
                    omega[i, j, a] * e[j, b] - omega[i, j, b] * e[j, a]
                    for j in range(n)
                )
    frame_a_I = np.linalg.inv(e)
    torsion_upper = np.einsum("aI,Ibc->abc", frame_a_I, torsion_internal)
    antisymmetry_residual = float(np.max(np.abs(torsion_upper + np.swapaxes(torsion_upper, 1, 2))))
    return {
        "q_ab": q.tolist(),
        "torsion_T_internal_I_ab": torsion_internal.tolist(),
        "torsion_T_upper_a_bc": torsion_upper.tolist(),
        "torsion_antisymmetry_residual_max_abs": antisymmetry_residual,
        "cartan_formula": "T^I_ab = de^I_ab + omega^I_J_a e^J_b - omega^I_J_b e^J_a",
    }


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    torsion = None
    if input_exists:
        try:
            source = _load_input(input_path)
            torsion = _cartan_torsion(
                source["q_ab"],
                source["coframe_e_I_a"],
                source["exterior_de_I_ab"],
                source["spin_connection_omega_IJ_a"],
            )
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "Sigma_torsion_pullback_ready": True,
                "selected_route": "cartan_pullback_components",
                **torsion,
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-torsion-pullback-components-from-coframe-connection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "torsion_pullback_components_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "coframe_connection_pullback_components_inputs",
        "validation_error": validation_error,
        "torsion_summary": torsion or {},
        "next_required": []
        if output_written
        else [
            "derive_active_q_ab_on_Sigma",
            "derive_coframe_pullback_e_I_a",
            "derive_exterior_derivative_de_I_ab",
            "derive_spin_connection_pullback_omega_IJ_a",
            "write_outputs_active_z2_sigma_coframe_connection_pullback_components_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Torsion Pullback Components From Coframe/Connection Gate",
        "",
        f"Output written: `{payload['torsion_pullback_components_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
