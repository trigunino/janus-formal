from __future__ import annotations

import itertools
import json
import math
import sys
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


INPUT_PATH = Path("outputs/active_z2_sigma/torsion_pullback_components_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/flrw_irreducible_torsion_components.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_irreducible_torsion_components_from_pullback_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_irreducible_torsion_components_from_pullback_gate.json")


def _levi_civita_symbol(indices: tuple[int, ...]) -> int:
    if len(set(indices)) != len(indices):
        return 0
    inversions = sum(1 for i in range(len(indices)) for j in range(i + 1, len(indices)) if indices[i] > indices[j])
    return -1 if inversions % 2 else 1


def _antisymmetrize_all(t_lower: np.ndarray) -> np.ndarray:
    n = t_lower.shape[0]
    out = np.zeros_like(t_lower)
    perms = list(itertools.permutations(range(3)))
    for a in range(n):
        for b in range(n):
            for c in range(n):
                value = 0.0
                base = [a, b, c]
                for perm in perms:
                    permuted = tuple(base[i] for i in perm)
                    sign = _levi_civita_symbol(perm)
                    value += sign * t_lower[permuted]
                out[a, b, c] = value / 6.0
    return out


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("torsion pullback active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("torsion pullback source must be active_derived")
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
    if payload.get("Sigma_torsion_pullback_ready") is not True:
        raise ValueError("Sigma_torsion_pullback_ready must be true")
    if payload.get("selected_route") != "cartan_pullback_components":
        raise ValueError("selected_route must be cartan_pullback_components")
    return payload


def _decompose(q_ab, torsion_upper):
    q = np.asarray(q_ab, dtype=float)
    torsion = np.asarray(torsion_upper, dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1] or q.shape[0] < 3:
        raise ValueError("q_ab must be a square metric with dimension >= 3")
    n = q.shape[0]
    if torsion.shape != (n, n, n):
        raise ValueError("torsion_T_upper_a_bc must have shape n x n x n")
    if not np.allclose(q, q.T, atol=1e-10):
        raise ValueError("q_ab must be symmetric")
    if not np.all(np.isfinite(q)) or not np.all(np.isfinite(torsion)):
        raise ValueError("q_ab and torsion_T_upper_a_bc must be finite")
    det_q = float(np.linalg.det(q))
    if not math.isfinite(det_q) or abs(det_q) < 1e-14:
        raise ValueError("q_ab must be non-degenerate")
    if not np.allclose(torsion + np.swapaxes(torsion, 1, 2), 0.0, atol=1e-8):
        raise ValueError("torsion_T_upper_a_bc must be antisymmetric in b,c")

    t_lower = np.einsum("ad,dbc->abc", q, torsion)
    trace = np.einsum("aac->c", torsion)
    trace_lower = q @ trace
    trace_piece = np.zeros_like(t_lower)
    for a in range(n):
        for b in range(n):
            for c in range(n):
                trace_piece[a, b, c] = (q[a, b] * trace_lower[c] - q[a, c] * trace_lower[b]) / (n - 1)

    axial_piece = _antisymmetrize_all(t_lower)
    tensor_piece = t_lower - trace_piece - axial_piece
    reconstruct = trace_piece + axial_piece + tensor_piece
    residual = float(np.max(np.abs(reconstruct - t_lower)))

    axial_dual_scalar = None
    if n == 3:
        eps_contra = np.zeros((3, 3, 3), dtype=float)
        scale = 1.0 / math.sqrt(abs(det_q))
        for idx in itertools.product(range(3), repeat=3):
            eps_contra[idx] = scale * _levi_civita_symbol(idx)
        axial_dual_scalar = float(np.einsum("abc,abc->", eps_contra, axial_piece))

    return {
        "dimension": n,
        "trace_vector_values": trace.tolist(),
        "trace_vector_component_ready": True,
        "axial_totally_antisymmetric_component_values": axial_piece.tolist(),
        "axial_dual_scalar_value": axial_dual_scalar,
        "axial_vector_component_ready": True,
        "tensor_torsion_values": tensor_piece.tolist(),
        "tensor_torsion_component_ready": True,
        "reconstruction_residual_max_abs": residual,
        "irreducible_decomposition_formula": (
            "T_abc = (q_ab T_c - q_ac T_b)/(n-1) + T_[abc] + q_abc"
        ),
    }


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    components = None
    if input_exists:
        try:
            source = _load_input(input_path)
            components = _decompose(source["q_ab"], source["torsion_T_upper_a_bc"])
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
                "selected_route": "FLRW_irreducible_torsion_from_Cartan_pullback",
                **components,
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-flrw-irreducible-torsion-components-from-pullback-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "FLRW_irreducible_components_from_pullback_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "torsion_pullback_components_inputs",
        "validation_error": validation_error,
        "components": components or {},
        "next_required": []
        if output_written
        else [
            "derive_active_q_ab_on_Sigma",
            "derive_active_torsion_T_upper_a_bc_pullback_on_Sigma",
            "write_outputs_active_z2_sigma_torsion_pullback_components_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Irreducible Torsion Components From Pullback Gate",
        "",
        f"Output written: `{payload['FLRW_irreducible_components_from_pullback_written']}`",
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
