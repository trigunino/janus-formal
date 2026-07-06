from __future__ import annotations

import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_to_flrw_extrinsic_curvature_input_gate import (
    INPUT_PATH as EMBEDDING_INPUT_PATH,
    OUTPUT_PATH as K_OUTPUT_PATH,
    build_payload as build_k_payload,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_plugstar_curvature_amplitude_from_embedding_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_plugstar_curvature_amplitude_from_embedding_gate.json"
)


def _finite_positive(values: list[float], field: str) -> list[float]:
    cleaned = [float(value) for value in values]
    if not cleaned or any(not math.isfinite(value) or value <= 0.0 for value in cleaned):
        raise ValueError(f"{field} must contain positive finite values")
    return cleaned


def _finite_values(values: list[float], field: str) -> list[float]:
    cleaned = [float(value) for value in values]
    if not cleaned or any(not math.isfinite(value) for value in cleaned):
        raise ValueError(f"{field} must contain finite values")
    return cleaned


def derive_active_a_k(embedding_payload: dict, k_payload: dict) -> dict:
    r_sigma = _finite_positive(embedding_payload["R_Sigma_of_a"], "R_Sigma_of_a")
    k_s_plus = _finite_values(k_payload["K_s_plus_Z2Sigma"], "K_s_plus_Z2Sigma")
    k_s_minus = _finite_values(k_payload["K_s_minus_Z2Sigma"], "K_s_minus_Z2Sigma")
    k_tau_plus = _finite_values(k_payload["K_tau_plus_Z2Sigma"], "K_tau_plus_Z2Sigma")
    k_tau_minus = _finite_values(k_payload["K_tau_minus_Z2Sigma"], "K_tau_minus_Z2Sigma")
    lengths = {len(r_sigma), len(k_s_plus), len(k_s_minus), len(k_tau_plus), len(k_tau_minus)}
    if len(lengths) != 1:
        raise ValueError("R_Sigma and K grids must have matching lengths")

    rows = []
    for index, radius in enumerate(r_sigma):
        plus_concentration = k_tau_plus[index] ** 2 + 3.0 * k_s_plus[index] ** 2
        minus_concentration = k_tau_minus[index] ** 2 + 3.0 * k_s_minus[index] ** 2
        selected = max(plus_concentration, minus_concentration)
        rows.append(
            {
                "index": index,
                "R_Sigma": radius,
                "C_K_plus": plus_concentration,
                "C_K_minus": minus_concentration,
                "C_K_selected": selected,
                "R2_C_K": radius * radius * selected,
            }
        )
    a_k = max(row["R2_C_K"] for row in rows)
    if not math.isfinite(a_k) or a_k <= 0.0:
        raise ValueError("A_K must be positive and finite")
    return {
        "A_K": a_k,
        "A_K_formula": "max_a R_Sigma(a)^2 * max(K_tau_plus^2 + 3*K_s_plus^2, K_tau_minus^2 + 3*K_s_minus^2)",
        "curvature_concentration_formula": "C_K = K_tau^2 + 3*K_s^2",
        "rows": rows,
    }


def build_payload(
    *,
    embedding_input_path: Path = EMBEDDING_INPUT_PATH,
    k_output_path: Path = K_OUTPUT_PATH,
) -> dict:
    k_gate = build_k_payload(input_path=embedding_input_path, output_path=k_output_path)
    embedding_payload = k_gate["input_manifest"]["payload"]
    k_payload = None
    derivation_error = None
    if k_gate["gate_passed"]:
        try:
            k_payload = json.loads(Path(k_gate["output_manifest"]).read_text(encoding="utf-8"))
            active_a_k = derive_active_a_k(embedding_payload, k_payload)
        except Exception as exc:
            active_a_k = None
            derivation_error = str(exc)
    else:
        active_a_k = None

    closure = {
        "R_Sigma_grid_available": embedding_payload is not None and "R_Sigma_of_a" in embedding_payload,
        "FLRW_K_grid_available": k_gate["gate_passed"],
        "curvature_concentration_declared": True,
        "curvature_concentration_Z2_even": True,
        "A_K_definition_declared": True,
        "A_K_positive_finite": active_a_k is not None,
        "R_Sigma_min_formula_uses_active_A_K": active_a_k is not None,
        "active_A_K_certificate_ready": active_a_k is not None,
    }
    gate_passed = all(closure.values())
    blockers = [key for key, value in closure.items() if not value]
    if derivation_error:
        blockers.append("A_K_derivation_error")
    archive_decision = {
        "archive_ready": True,
        "archive_status": "ready_to_archive_with_blocker"
        if not gate_passed
        else "ready_to_archive_with_active_A_K_certificate",
        "final_verdict": "active_A_K_adapter_complete",
        "unresolved_active_blocker": "none" if gate_passed else blockers[0],
        "does_not_write_fake_active_manifest": True,
        "active_pipeline_import_forbidden": not gate_passed,
    }

    return {
        "status": "janus-z2-sigma-plugstar-curvature-amplitude-from-embedding-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_embedding_curvature_derived",
        "route": "SigmaPlugstarCurvatureAmplitudeFromEmbeddingGate",
        "declared": {
            "active_embedding_to_FLRW_K_imported": True,
            "plugstar_threshold_gate_imported": True,
            "observational_fit_forbidden": True,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        },
        "closure": closure,
        "active_A_K_certificate": active_a_k,
        "threshold_solution": None
        if active_a_k is None
        else {
            "equation": "A_K / R_Sigma^2 = K_crit^2",
            "A_K": active_a_k["A_K"],
            "R_Sigma_min": "sqrt(A_K) / K_crit",
            "active_bound": f"R_Sigma(a) >= sqrt({active_a_k['A_K']:.12g}) / K_crit",
        },
        "upstream_embedding_to_k_gate": {
            "status": k_gate["status"],
            "gate_passed": k_gate["gate_passed"],
            "primary_blocker": k_gate["primary_blocker"],
            "K_reduction_route": k_gate["K_reduction_route"],
            "nearest_blocks": k_gate["nearest_embedding_to_flrw_K_frontier"]["blocks"],
        },
        "derivation_error": derivation_error,
        "gate_passed": gate_passed,
        "route_status": "active_A_K_derived" if gate_passed else "blocked_waiting_for_active_embedding_K_grid",
        "primary_blocker": "none" if gate_passed else blockers[0],
        "blockers": blockers,
        "archive_decision": archive_decision,
        "interpretation": (
            "A_K is now tied to active embedding curvature data: it is the grid supremum "
            "of R_Sigma^2 times the Z2-even FLRW extrinsic-curvature concentration."
        ),
        "next_required": []
        if gate_passed
        else [
            "write_active_tunnel_embedding_geometry_inputs_with_R_Sigma_and_K_or_second_form",
            "pass_active_embedding_to_FLRW_extrinsic_curvature_input_gate",
            "then_regenerate_active_A_K_certificate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Plugstar Curvature Amplitude From Embedding Gate",
        "",
        f"Route status: `{payload['route_status']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
    ]
    if payload["threshold_solution"] is not None:
        lines.extend(["", "## Threshold Solution"])
        lines.extend(
            f"- `{key}`: `{value}`" for key, value in payload["threshold_solution"].items()
        )
    lines.extend(["", "## Archive Decision"])
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in payload["archive_decision"].items()
    )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
