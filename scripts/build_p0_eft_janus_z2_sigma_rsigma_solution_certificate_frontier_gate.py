from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_rsigma_radial_terms import (
    load_active_z2sigma_rsigma_radial_term_manifest,
)
from scripts.derive_p0_eft_janus_z2_sigma_remaining_non_ghy_counterterm_channel_audit import (
    build_payload as build_remaining_non_ghy_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_radial_block_gate import (
    build_payload as build_cartan_ghy_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_first_action_assembly_gate import (
    build_payload as build_active_first_action_payload,
)


TERM_PATHS = {
    "E_HolstNiehYan": Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json"),
    "E_matterFlux": Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json"),
    "E_counterterm": Path("outputs/active_z2_sigma/rsigma_E_counterterm.json"),
}
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_solution_certificate_frontier_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_solution_certificate_frontier_gate.json"
)


def _term_status(name: str, path: Path) -> dict:
    if not path.exists():
        return {"exists": False, "all_zero": None, "values": None}
    payload = load_active_z2sigma_rsigma_radial_term_manifest(path, expected_term_name=name)
    values = [float(value) for value in payload["term_values"]]
    return {
        "exists": True,
        "all_zero": all(value == 0.0 for value in values),
        "values": values,
        "provenance": payload["term_provenance"],
    }


def build_payload(*, term_paths: dict[str, Path] = TERM_PATHS) -> dict:
    terms = {name: _term_status(name, path) for name, path in term_paths.items()}
    remaining = build_remaining_non_ghy_payload()
    cartan_ghy = build_cartan_ghy_payload()
    active_action = build_active_first_action_payload()
    counterterm_missing = not terms["E_counterterm"]["exists"]
    known_noncartan_zero = (
        terms["E_HolstNiehYan"]["exists"]
        and terms["E_HolstNiehYan"]["all_zero"]
        and terms["E_matterFlux"]["exists"]
        and terms["E_matterFlux"]["all_zero"]
    )
    finite_certificate_blocked = counterterm_missing or (
        known_noncartan_zero and terms["E_counterterm"]["all_zero"] is True
    )
    return {
        "status": "janus-z2-sigma-rsigma-solution-certificate-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "terms": terms,
        "cartan_ghy_symbolic_R_block": cartan_ghy["symbolic_R_block"],
        "cartan_ghy_symbolic_R_block_ready": cartan_ghy[
            "cartan_ghy_symbolic_R_block_ready"
        ],
        "cartan_ghy_numeric_of_a_ready": cartan_ghy[
            "cartan_ghy_radial_block_of_a_ready"
        ],
        "known_noncartan_without_counterterm_zero": known_noncartan_zero,
        "counterterm_radial_term_available": terms["E_counterterm"]["exists"],
        "finite_RSigma_certificate_currently_possible": not finite_certificate_blocked,
        "gate_passed": not finite_certificate_blocked,
        "remaining_non_GHY_counterterm_channels": remaining["open_non_GHY_channels"],
        "open_remaining_non_GHY_counterterm_channels": [
            name for name, is_open in remaining["open_non_GHY_channels"].items() if is_open
        ],
        "active_first_action": {
            "assembled": active_action["gate_passed"],
            "primary_blocker": active_action["primary_blocker"],
            "blockers": active_action["blockers"],
            "S_cross_source_accepted": active_action["upstream"]["cross_action"][
                "source_accepted"
            ],
        },
        "post_radius_embedding_channels": remaining["post_radius_embedding_channels"],
        "post_radius_embedding_manifest_route": {
            "gate": "P0EFTJanusZ2SigmaRSigmaSolutionToEmbeddingCurvatureBranchGate",
            "prepared": True,
            "output_manifest": "outputs/active_z2_sigma/active_tunnel_embedding_geometry_inputs.json",
            "unblocked_only_by": "active_no_fit_R_Sigma_solution_certificate",
            "does_not_close_S_cross_or_Bianchi": True,
        },
        "primary_blocker": "none"
        if not finite_certificate_blocked
        else (
            "counterterm_trace_residual_inputs_R_h_R_K"
            if counterterm_missing
            else "nonzero_noncartan_radial_balance"
        ),
        "interpretation": (
            "Current active Holst/Nieh-Yan and matter-flux radial blocks vanish. "
            "A finite positive R_Sigma certificate therefore requires a derived "
            "counterterm radial block that balances the symbolic Cartan-GHY term "
            "E_CartanGHY(R)=6 eps sqrt(det(q)) R/kappa, or another source-derived "
            "non-Cartan radial block. Otherwise the isotropic balance has only the "
            "degenerate R_Sigma -> 0 frontier and must not be promoted as a finite throat."
        ),
        "next_required": [
            "use_symbolic_E_CartanGHY_of_R_in_E_RSigma_before_solving_R_Sigma_of_a",
            "derive_or_eliminate_metric_non_GHY_trace_R_h",
            "derive_or_eliminate_extrinsic_non_GHY_trace_R_K",
            "then_materialize_counterterm_trace_residual_inputs",
            "run_counterterm_minimal_basis_coefficient_solver_gate",
            "run_counterterm_lct_profile_from_minimal_coefficients_gate",
            "then_derive_counterterm_radial_density_variation_inputs",
            "write_rsigma_E_counterterm_json",
            "write_rsigma_certificate_payload_json",
            "run_rsigma_isotropic_balance_solver_gate",
            "then_run_rsigma_solution_to_embedding_curvature_branch_gate",
            "keep_S_cross_blocker_separate_from_RSigma_counterterm_trace_blocker",
        ],
        "forbidden_shortcuts": [
            "do_not_set_E_counterterm_to_zero_and_claim_finite_RSigma",
            "do_not_use_toy_exact_model_as_certificate",
            "do_not_fit_counterterm_density",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Solution Certificate Frontier Gate",
        "",
        f"Finite certificate currently possible: `{payload['finite_RSigma_certificate_currently_possible']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    lines.extend(["", "## Forbidden Shortcuts"])
    lines.extend(f"- `{item}`" for item in payload["forbidden_shortcuts"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
