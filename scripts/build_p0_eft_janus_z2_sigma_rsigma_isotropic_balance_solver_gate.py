from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_rsigma_isotropic_solver import solve_isotropic_rsigma_balance
from janus_lab.z2_sigma_rsigma_radial_terms import (
    load_active_z2sigma_rsigma_radial_term_manifest,
    write_active_z2sigma_rsigma_radial_term_manifest,
)
from janus_lab.z2_sigma_rsigma_certificate import write_active_z2sigma_rsigma_solution_certificate


TERM_PATHS = {
    "E_HolstNiehYan": Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json"),
    "E_matterFlux": Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json"),
    "E_counterterm": Path("outputs/active_z2_sigma/rsigma_E_counterterm.json"),
}
Q_INPUT_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
CERTIFICATE_PAYLOAD_PATH = Path("outputs/active_z2_sigma/rsigma_certificate_payload.json")
CERTIFICATE_OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_solution_certificate.json")
CARTAN_OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_E_CartanGHY.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_isotropic_balance_solver_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_isotropic_balance_solver_gate.json")


def _load_q(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("q_ab active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("q_ab source must be active_derived")
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


def build_payload(
    *,
    term_paths: dict[str, Path] = TERM_PATHS,
    q_input_path: Path = Q_INPUT_PATH,
    certificate_payload_path: Path = CERTIFICATE_PAYLOAD_PATH,
    certificate_output_path: Path = CERTIFICATE_OUTPUT_PATH,
    cartan_output_path: Path = CARTAN_OUTPUT_PATH,
) -> dict:
    input_exists = {name: path.exists() for name, path in term_paths.items()}
    input_exists["unit_intrinsic_metric_q_ab"] = q_input_path.exists()
    input_exists["certificate_payload"] = certificate_payload_path.exists()
    solved = False
    validation_error = None
    residual_max_abs = None
    if all(input_exists.values()):
        try:
            terms = {
                name: load_active_z2sigma_rsigma_radial_term_manifest(path, expected_term_name=name)
                for name, path in term_paths.items()
            }
            q_payload = _load_q(q_input_path)
            certificate_payload = json.loads(certificate_payload_path.read_text(encoding="utf-8"))
            grid = terms["E_HolstNiehYan"]["a_grid"]
            certificate, cartan_term = solve_isotropic_rsigma_balance(
                a_grid=grid,
                E_HolstNiehYan=terms["E_HolstNiehYan"]["term_values"],
                E_matterFlux=terms["E_matterFlux"]["term_values"],
                E_counterterm=terms["E_counterterm"]["term_values"],
                unit_intrinsic_metric_q_ab=q_payload["unit_intrinsic_metric_q_ab"],
                kappa_Z2Sigma=q_payload["kappa_Z2Sigma"],
                z2_orientation_sign=certificate_payload["z2_orientation_sign"],
                certificate_payload=certificate_payload,
                term_provenance={
                    "E_CartanGHY": "active isotropic Cartan-GHY balance solver",
                    "E_HolstNiehYan": terms["E_HolstNiehYan"]["term_provenance"],
                    "E_matterFlux": terms["E_matterFlux"]["term_provenance"],
                    "E_counterterm": terms["E_counterterm"]["term_provenance"],
                },
            )
            write_active_z2sigma_rsigma_solution_certificate(certificate_output_path, certificate)
            write_active_z2sigma_rsigma_radial_term_manifest(cartan_output_path, cartan_term)
            residual_max_abs = certificate["R_Sigma_solution_residual_max_abs"]
            solved = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rsigma-isotropic-balance-solver-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "certificate_output": str(certificate_output_path),
        "cartan_output": str(cartan_output_path),
        "R_Sigma_solution_residual_max_abs": residual_max_abs,
        "isotropic_balance_solved": solved,
        "gate_passed": solved,
        "primary_blocker": "none" if solved else "R_Sigma_isotropic_balance_inputs",
        "validation_error": validation_error,
        "next_required": []
        if solved
        else [
            "provide_non_Cartan_radial_term_manifests",
            "provide_unit_intrinsic_metric_q_ab_inputs_json",
            "provide_rsigma_certificate_payload_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Isotropic Balance Solver Gate",
        "",
        f"Solved: `{payload['isotropic_balance_solved']}`",
        f"Residual max abs: `{payload['R_Sigma_solution_residual_max_abs']}`",
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
