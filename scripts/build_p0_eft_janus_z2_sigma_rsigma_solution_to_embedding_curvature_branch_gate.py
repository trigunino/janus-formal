from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate import (
    build_payload as build_throat_radius_frontier_payload,
)
from janus_lab.z2_sigma_rsigma_certificate import (
    REQUIRED_RSIGMA_CERTIFICATE_FIELDS as REQUIRED_CERTIFICATE_FIELDS,
    load_active_z2sigma_rsigma_solution_certificate,
)


INPUT_PATH = Path("outputs/active_z2_sigma/rsigma_solution_certificate.json")
EMBEDDING_OUTPUT_PATH = Path("outputs/active_z2_sigma/active_tunnel_embedding_geometry_inputs.json")
CURVATURE_OUTPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_branch_inputs.json")
H0_NORMALIZATION_OUTPUT_PATH = Path("outputs/active_z2_sigma/background_H0_normalization_inputs.json")
CURVATURE_RADIUS_NORMALIZATION_OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/background_curvature_radius_normalization_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_solution_to_embedding_curvature_branch_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_solution_to_embedding_curvature_branch_gate.json"
)

def _certificate_status(path: Path) -> dict:
    exists = path.exists()
    missing_fields: list[str] = []
    validation_error = None
    certificate_type = None
    is_template = None
    not_solution_certificate = None
    if exists:
        try:
            payload = load_active_z2sigma_rsigma_solution_certificate(path)
            missing_fields = [field for field in REQUIRED_CERTIFICATE_FIELDS if field not in payload]
            certificate_type = payload.get("R_Sigma_solution_certificate_type")
            is_template = bool(payload.get("rsigma_payload_is_template", False))
            not_solution_certificate = bool(payload.get("rsigma_payload_not_solution_certificate", False))
        except Exception as exc:
            validation_error = str(exc)
    active_no_fit_solution_ready = (
        certificate_type == "active_no_fit_solution"
        and is_template is False
        and not_solution_certificate is False
        and validation_error is None
        and not missing_fields
    )
    return {
        "path": str(path),
        "exists": exists,
        "missing_fields": missing_fields,
        "validation_error": validation_error,
        "R_Sigma_solution_certificate_type": certificate_type,
        "rsigma_payload_is_template": is_template,
        "rsigma_payload_not_solution_certificate": not_solution_certificate,
        "active_no_fit_solution_certificate_ready": active_no_fit_solution_ready,
    }


def _load_certificate(path: Path) -> dict:
    return load_active_z2sigma_rsigma_solution_certificate(path)


def _build_embedding_manifest(cert: dict) -> dict:
    manifest = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": cert["a_grid"],
        "R_Sigma_of_a": cert["R_Sigma_of_a"],
        "X_plus_of_a": cert["X_plus_of_a"],
        "X_minus_of_a": cert["X_minus_of_a"],
        "tangent_frames_plus": cert["tangent_frames_plus"],
        "tangent_frames_minus": cert["tangent_frames_minus"],
        "unit_normals_plus": cert["unit_normals_plus"],
        "unit_normals_minus": cert["unit_normals_minus"],
        "christoffels_plus": cert["christoffels_plus"],
        "christoffels_minus": cert["christoffels_minus"],
        "spatial_inverse_metric": cert["spatial_inverse_metric"],
        "z2_orientation_sign": cert["z2_orientation_sign"],
        "embedding_provenance": cert["rsigma_solution_provenance"],
        "effective_RSigma_equation": cert["effective_RSigma_equation"],
    }
    for field in [
        "second_embedding_plus",
        "second_embedding_minus",
        "tau_index",
        "spatial_indices",
    ]:
        if field in cert:
            manifest[field] = cert[field]
    return manifest


def _build_curvature_branch_manifest(cert: dict) -> dict:
    provenance = str(cert["rsigma_solution_provenance"])
    h0 = float(cert["H0_Z2Sigma_km_s_Mpc"])
    r_curv = float(cert["R_curv_Z2Sigma_Mpc"])
    k_value = int(cert["k_Z2Sigma"])
    if h0 <= 0.0:
        raise ValueError("H0_Z2Sigma_km_s_Mpc must be positive")
    if r_curv <= 0.0:
        raise ValueError("R_curv_Z2Sigma_Mpc must be positive")
    if k_value not in [-1, 0, 1]:
        raise ValueError("k_Z2Sigma must be -1, 0, or 1")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": h0,
            "R_curv_Z2Sigma_Mpc": r_curv,
            "k_Z2Sigma": k_value,
        },
        "scalar_provenance": {
            "H0_Z2Sigma": f"active_RSigma_solution_certificate:({provenance})",
            "R_curv_Z2Sigma": f"active_RSigma_solution_certificate:({provenance})",
            "k_Z2Sigma": f"active_RSigma_solution_certificate:({provenance})",
        },
        "source_effective_RSigma_equation": cert["effective_RSigma_equation"],
        "spatial_topology": cert.get(
            "spatial_topology",
            {"quotient_spatial_slice": "S3_paired_leaf_representative"},
        ),
    }


def _build_h0_normalization_manifest(cert: dict) -> dict:
    provenance = str(cert["rsigma_solution_provenance"])
    h0 = float(cert["H0_Z2Sigma_km_s_Mpc"])
    if h0 <= 0.0:
        raise ValueError("H0_Z2Sigma_km_s_Mpc must be positive")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {"H0_Z2Sigma_km_s_Mpc": h0},
        "scalar_provenance": {
            "H0_Z2Sigma": f"active_RSigma_solution_certificate:({provenance})"
        },
        "source_effective_RSigma_equation": cert["effective_RSigma_equation"],
    }


def _build_curvature_radius_normalization_manifest(cert: dict) -> dict:
    provenance = str(cert["rsigma_solution_provenance"])
    r_curv = float(cert["R_curv_Z2Sigma_Mpc"])
    if r_curv <= 0.0:
        raise ValueError("R_curv_Z2Sigma_Mpc must be positive")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "scalars": {"R_curv_Z2Sigma_Mpc": r_curv},
        "scalar_provenance": {
            "R_curv_Z2Sigma": f"active_RSigma_solution_certificate:({provenance})"
        },
        "source_effective_RSigma_equation": cert["effective_RSigma_equation"],
    }


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    embedding_output_path: Path = EMBEDDING_OUTPUT_PATH,
    curvature_output_path: Path = CURVATURE_OUTPUT_PATH,
    h0_normalization_output_path: Path = H0_NORMALIZATION_OUTPUT_PATH,
    curvature_radius_normalization_output_path: Path = CURVATURE_RADIUS_NORMALIZATION_OUTPUT_PATH,
    frontier_payload: dict | None = None,
) -> dict:
    frontier = frontier_payload if frontier_payload is not None else build_throat_radius_frontier_payload()
    certificate = _certificate_status(input_path)
    status_flags = frontier.get("status_flags", {})
    matter_flux_reduced = bool(status_flags.get("matter_flux_block_reduced", False))
    counterterm_reduced = bool(status_flags.get("counterterm_block_reduced", False))
    radius_ready = bool(status_flags.get("R_Sigma_of_a_ready", False))
    solution_certificate_ready = bool(frontier.get("throat_radius_solution_certificate_ready", False))
    embedding_unblocked = bool(frontier.get("embedding_unblocked_by_radius_solution", False))
    bridge_frontier_ready = (
        matter_flux_reduced
        and counterterm_reduced
        and radius_ready
        and solution_certificate_ready
        and embedding_unblocked
    )
    can_write = (
        bridge_frontier_ready
        and certificate["exists"]
        and not certificate["missing_fields"]
        and certificate["validation_error"] is None
        and certificate["active_no_fit_solution_certificate_ready"]
    )
    embedding_written = False
    curvature_written = False
    h0_normalization_written = False
    curvature_radius_normalization_written = False
    write_error = None
    if can_write:
        try:
            cert = _load_certificate(input_path)
            embedding_output_path.parent.mkdir(parents=True, exist_ok=True)
            curvature_output_path.parent.mkdir(parents=True, exist_ok=True)
            h0_normalization_output_path.parent.mkdir(parents=True, exist_ok=True)
            curvature_radius_normalization_output_path.parent.mkdir(parents=True, exist_ok=True)
            embedding_output_path.write_text(
                json.dumps(_build_embedding_manifest(cert), indent=2),
                encoding="utf-8",
            )
            curvature_output_path.write_text(
                json.dumps(_build_curvature_branch_manifest(cert), indent=2),
                encoding="utf-8",
            )
            h0_normalization_output_path.write_text(
                json.dumps(_build_h0_normalization_manifest(cert), indent=2),
                encoding="utf-8",
            )
            curvature_radius_normalization_output_path.write_text(
                json.dumps(_build_curvature_radius_normalization_manifest(cert), indent=2),
                encoding="utf-8",
            )
            embedding_written = True
            curvature_written = True
            h0_normalization_written = True
            curvature_radius_normalization_written = True
        except Exception as exc:
            write_error = str(exc)
            can_write = False
    return {
        "status": "janus-z2-sigma-rsigma-solution-to-embedding-curvature-branch-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_certificate": certificate,
        "embedding_output_manifest": str(embedding_output_path),
        "curvature_output_manifest": str(curvature_output_path),
        "h0_normalization_output_manifest": str(h0_normalization_output_path),
        "curvature_radius_normalization_output_manifest": str(
            curvature_radius_normalization_output_path
        ),
        "bridge_declared": True,
        "required_certificate_fields": REQUIRED_CERTIFICATE_FIELDS,
        "throat_radius_frontier_ready": bridge_frontier_ready,
        "throat_radius_frontier": {
            "matter_flux_block_reduced": matter_flux_reduced,
            "counterterm_block_reduced": counterterm_reduced,
            "R_Sigma_of_a_ready": status_flags.get("R_Sigma_of_a_ready"),
            "throat_radius_solution_certificate_ready": solution_certificate_ready,
            "embedding_unblocked_by_radius_solution": embedding_unblocked,
        },
        "would_write_embedding_manifest": can_write,
        "would_write_curvature_branch_manifest": can_write,
        "would_write_h0_normalization_manifest": can_write,
        "would_write_curvature_radius_normalization_manifest": can_write,
        "embedding_manifest_written": embedding_written,
        "curvature_branch_manifest_written": curvature_written,
        "h0_normalization_manifest_written": h0_normalization_written,
        "curvature_radius_normalization_manifest_written": curvature_radius_normalization_written,
        "gate_passed": (
            can_write
            and embedding_written
            and curvature_written
            and h0_normalization_written
            and curvature_radius_normalization_written
        ),
        "primary_blocker": (
            "none"
            if can_write
            else "R_Sigma_solution_certificate_from_coupled_radius_flux_system"
        ),
        "validation_error": write_error,
        "blocker": None
        if can_write
        else "R_Sigma(a) active no-fit solution certificate is unavailable or throat radius frontier is not closed",
        "next_required": [
            "reduce_matter_flux_or_solve_coupled_radius_flux_system",
            "reduce_counterterm_radial_block",
            "derive_R_Sigma_of_a_from_throat_variational_equation",
            "then_write_embedding_and_curvature_branch_manifests",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Solution To Embedding/Curvature Branch Gate",
        "",
        f"Bridge declared: `{payload['bridge_declared']}`",
        f"Throat radius frontier ready: `{payload['throat_radius_frontier_ready']}`",
        f"Certificate exists: `{payload['input_certificate']['exists']}`",
        f"Would write embedding manifest: `{payload['would_write_embedding_manifest']}`",
        f"Would write curvature branch manifest: `{payload['would_write_curvature_branch_manifest']}`",
        f"Would write H0 normalization manifest: `{payload['would_write_h0_normalization_manifest']}`",
        (
            "Would write curvature radius normalization manifest: "
            f"`{payload['would_write_curvature_radius_normalization_manifest']}`"
        ),
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
