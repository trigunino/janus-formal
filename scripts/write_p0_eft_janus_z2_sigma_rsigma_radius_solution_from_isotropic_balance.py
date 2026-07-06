from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.z2_sigma_rsigma_radial_terms import load_active_z2sigma_rsigma_radial_term_manifest


TERM_PATHS = {
    "E_HolstNiehYan": Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json"),
    "E_matterFlux": Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json"),
    "E_counterterm": Path("outputs/active_z2_sigma/rsigma_E_counterterm.json"),
}
Q_INPUT_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
FRAME_INPUT_PATH = Path("outputs/active_z2_sigma/sigma_unit_frame_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_radius_solution.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_radius_solution_from_isotropic_balance.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_radius_solution_from_isotropic_balance.json")


def _load_q(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma" or payload.get("source") != "active_derived":
        raise ValueError("q_ab payload must be active Z2_tunnel_Sigma / active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def _load_orientation(path: Path) -> float:
    payload = json.loads(path.read_text(encoding="utf-8"))
    value = float(payload["z2_orientation_sign"])
    if value not in (-1.0, 1.0):
        raise ValueError("z2_orientation_sign must be +/-1")
    return value


def build_payload(
    *,
    term_paths: dict[str, Path] = TERM_PATHS,
    q_input_path: Path = Q_INPUT_PATH,
    frame_input_path: Path = FRAME_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {name: path.exists() for name, path in term_paths.items()}
    input_exists["unit_intrinsic_metric_q_ab"] = q_input_path.exists()
    input_exists["sigma_unit_frame"] = frame_input_path.exists()
    if not all(input_exists.values()):
        return {
            "status": "janus-z2-sigma-rsigma-radius-solution-from-isotropic-balance",
            "active_core": "Z2_tunnel_Sigma",
            "input_exists": input_exists,
            "output_manifest": str(output_path),
            "radius_solution_written": False,
            "gate_passed": False,
            "primary_blocker": "minimal_rsigma_balance_inputs_missing",
        }

    validation_error = None
    try:
        terms = {
            name: load_active_z2sigma_rsigma_radial_term_manifest(path, expected_term_name=name)
            for name, path in term_paths.items()
        }
        q_payload = _load_q(q_input_path)
        eps = _load_orientation(frame_input_path)
        grid = np.asarray(terms["E_HolstNiehYan"]["a_grid"], dtype=float)
        for name, term in terms.items():
            if np.asarray(term["a_grid"], dtype=float).shape != grid.shape or not np.allclose(
                term["a_grid"], grid
            ):
                raise ValueError(f"{name} a_grid must match")
        q = np.asarray(q_payload["unit_intrinsic_metric_q_ab"], dtype=float)
        det_q = float(np.linalg.det(q))
        d = q.shape[0]
        if d <= 2:
            raise ValueError("intrinsic dimension must be > 2")
        coeff = eps * np.sqrt(abs(det_q)) * d * (d - 1) / float(q_payload["kappa_Z2Sigma"])
        noncartan = sum(np.asarray(terms[name]["term_values"], dtype=float) for name in terms)
        target = -noncartan / coeff
        if np.any(target <= 0.0) or not np.all(np.isfinite(target)):
            raise ValueError("isotropic balance does not yield positive R_Sigma")
        radius = target ** (1.0 / float(d - 2))
        manifest = {
            "active_core": "Z2_tunnel_Sigma",
            "source": "active_derived",
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
            "phenomenological_holst_bao_scan_used": False,
            "observational_fit_used": False,
            "a_grid": grid.tolist(),
            "R_Sigma_of_a": radius.tolist(),
            "z2_orientation_sign": eps,
            "rsigma_solution_provenance": "minimal active isotropic balance from non-Cartan radial terms",
            "term_provenance": {name: terms[name]["term_provenance"] for name in terms},
            "isotropic_balance_coefficient": coeff,
        }
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
        written = True
    except Exception as exc:
        validation_error = str(exc)
        written = False
    return {
        "status": "janus-z2-sigma-rsigma-radius-solution-from-isotropic-balance",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "radius_solution_written": written,
        "gate_passed": written,
        "primary_blocker": "none" if written else "invalid_minimal_rsigma_balance_inputs",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma R_Sigma Radius Solution From Isotropic Balance",
                "",
                f"Written: `{payload['radius_solution_written']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
