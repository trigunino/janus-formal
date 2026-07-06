from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_hamiltonian_scalar_targets_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_hamiltonian_scalar_targets_gate.json"
)


def build_payload() -> dict:
    targets = {
        "H0_Z2Sigma": {
            "status": "boundary_hamiltonian_constraint_target",
            "source_route": (
                "3+1 projected first-order boundary Hamiltonian: lapse times "
                "Hamiltonian constraint plus surface generator"
            ),
            "not_independent_density": True,
            "numeric_value_ready": False,
            "required_derivation": [
                "project theta_Holst_Palatini to 3+1 ADM boundary generator",
                "fix active time gauge/lapse normalization on Sigma",
                "evaluate on-shell Hamiltonian constraint for the active FLRW branch",
            ],
        },
        "R_curv_Z2Sigma_m": {
            "status": "gauss_codazzi_volume_surface_target",
            "source_route": (
                "Gauss-Codazzi plus projected spatial slice volume/surface "
                "normalization from the active Z2/Sigma tunnel branch"
            ),
            "not_independent_density": True,
            "numeric_value_ready": False,
            "required_derivation": [
                "derive active intrinsic spatial slice curvature sign and scale",
                "connect R3_Z2Sigma to the boundary/volume projection",
                "fix dimensional scale through the same Hamiltonian projection as H0",
            ],
        },
        "N_occ": {
            "status": "initial_state_or_superselection_target",
            "source_route": (
                "projected Noether charge reduction gives Q_Sigma=N_occ, but "
                "conservation alone does not select the occupation number"
            ),
            "not_independent_density": True,
            "numeric_value_ready": False,
            "required_derivation": [
                "derive boundary state-selection law from the spinor/projector sector",
                "or declare N_occ as explicit effective initial state datum",
            ],
        },
    }
    return {
        "status": "janus-z2-sigma-boundary-hamiltonian-scalar-targets-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "bibliography_guided_target_reduction",
        "bibliography_basis": [
            "Holst boundary theta and surface terms",
            "first-order topological terms and boundary charges",
            "3+1 Hamiltonian surface generator",
            "tetrad-metric exact boundary 3-form mismatch",
            "corner terms for nonsmooth boundaries",
        ],
        "targets": targets,
        "all_targets_numeric_ready": False,
        "background_scalars_ready": False,
        "early_plasma_ready": False,
        "forbidden_shortcuts": [
            "do_not_fit_H0_Z2Sigma",
            "do_not_fit_R_curv_Z2Sigma_m",
            "do_not_treat_N_occ_as_density_without_state",
            "do_not_import_Planck_LCDM_compressed_background",
        ],
        "next_required": [
            "derive_3plus1_boundary_hamiltonian_projection_for_H0",
            "derive_Gauss_Codazzi_volume_surface_projection_for_R_curv",
            "derive_spinor_boundary_state_selection_or_mark_N_occ_effective_initial_data",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Hamiltonian Scalar Targets Gate",
        "",
        "The missing scalars are classified as boundary/constraint targets, not free densities.",
        "",
        f"Background scalars ready: `{payload['background_scalars_ready']}`",
        f"Early plasma ready: `{payload['early_plasma_ready']}`",
        "",
        "## Targets",
    ]
    for name, target in payload["targets"].items():
        lines.extend(
            [
                f"- `{name}`: `{target['status']}`",
                f"  - numeric ready: `{target['numeric_value_ready']}`",
                f"  - route: {target['source_route']}",
            ]
        )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
