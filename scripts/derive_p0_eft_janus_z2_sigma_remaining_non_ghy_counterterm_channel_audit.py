from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate import (
    build_payload as build_spinor_residual_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_connection_residual_channel_gate import (
    build_payload as build_connection_residual_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_embedding_residual_channel_gate import (
    build_payload as build_embedding_residual_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_matter_flux_residual_channel_gate import (
    build_payload as build_matter_flux_residual_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_density_basis_gate import (
    build_payload as build_minimal_density_basis_payload,
)

ALPHA_PATH = Path("outputs/active_z2_sigma/counterterm_alpha_res_partial.json")
COEFF_PATH = Path("outputs/active_z2_sigma/counterterm_residual_coefficients_partial.json")
PARTITION_PATH = Path("outputs/active_z2_sigma/cartan_ghy_junction_trace_partition_audit.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/remaining_non_ghy_counterterm_channel_audit.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_remaining_non_ghy_counterterm_channel_audit.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_remaining_non_ghy_counterterm_channel_audit.json"
)


def _load_if_exists(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    *,
    alpha_path: Path = ALPHA_PATH,
    coeff_path: Path = COEFF_PATH,
    partition_path: Path = PARTITION_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    alpha = _load_if_exists(alpha_path)
    coeff = _load_if_exists(coeff_path)
    partition = _load_if_exists(partition_path)
    spinor = build_spinor_residual_payload()
    connection = build_connection_residual_payload()
    embedding = build_embedding_residual_payload()
    matter_flux = build_matter_flux_residual_payload()
    basis = build_minimal_density_basis_payload()
    spinor_ready = bool(spinor["counterterm_spinor_residual_channel_ready"])
    immirzi_term = next(
        term
        for term in basis["candidate_terms"]
        if term["name"] == "immirzi_radion_gradient"
    )
    immirzi_excluded_from_active_basis = bool(
        basis["declared"]["torsionless_branch_filter_declared"]
        and immirzi_term["kept"] is False
    )
    known_zero = {
        "linear_K_GHY_channel": bool(
            partition.get("partition", {}).get("linear_K_counterterm_residual_after_partition") == "0"
        ),
        "torsion_pullback_channel": bool(coeff.get("R_T_A_ready") and all(
            float(value) == 0.0
            for block in coeff.get("R_T_A_values", [])
            for row in block
            for value in row
        )),
        "immirzi_radial_contraction": bool(
            coeff.get("R_chi_partial_R_chi_ready")
            and all(float(value) == 0.0 for value in coeff.get("R_chi_partial_R_chi_values", []))
        ),
        "local_projected_spinor_residual_channel": spinor_ready,
        "perfect_fluid_matter_flux_residual_channel": bool(
            matter_flux["counterterm_matter_flux_residual_channel_ready"]
        ),
        "full_immirzi_nonradial_channel": bool(
            coeff.get("R_chi_partial_R_chi_ready")
            and all(float(value) == 0.0 for value in coeff.get("R_chi_partial_R_chi_values", []))
            and immirzi_excluded_from_active_basis
        ),
    }
    post_radius_channels = {
        "embedding_residual_channel": not bool(
            embedding["counterterm_embedding_residual_channel_ready"]
        ),
    }
    open_channels = {
        "metric_non_GHY_trace_R_h": not bool(coeff.get("R_h_ab_ready", False)),
        "extrinsic_non_GHY_trace_R_K": not bool(coeff.get("R_K_ab_ready", False)),
        "full_immirzi_nonradial_R_chi": not known_zero["full_immirzi_nonradial_channel"],
        "spinor_residual_channel": not spinor_ready,
        "connection_residual_channel": not bool(
            connection["counterterm_connection_residual_channel_ready"]
        ),
        "matter_flux_residual_channel": not bool(
            matter_flux["counterterm_matter_flux_residual_channel_ready"]
        ),
    }
    all_known_zero = all(known_zero.values())
    any_open = any(open_channels.values())
    open_labels = [
        label
        for label, is_open in open_channels.items()
        if is_open
    ]
    payload = {
        "status": "janus-z2-sigma-remaining-non-ghy-counterterm-channel-audit",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_residual_channel_audit",
        "inputs_present": {
            "alpha_res_partial": alpha_path.exists(),
            "partial_coefficients": coeff_path.exists(),
            "linear_K_partition": partition_path.exists(),
        },
        "known_zero_after_partition": known_zero,
        "spinor_residual_channel": {
            "gate": spinor["status"],
            "ready": spinor_ready,
            "coefficients": spinor["projected_residual_coefficients"],
        },
        "residual_channel_frontiers": {
            "connection": {
                "gate": connection["status"],
                "ready": connection["counterterm_connection_residual_channel_ready"],
                "closure": connection["closure"],
            },
            "embedding": {
                "gate": embedding["status"],
                "ready": embedding["counterterm_embedding_residual_channel_ready"],
                "closure": embedding["closure"],
            },
            "matter_flux": {
                "gate": matter_flux["status"],
                "ready": matter_flux["counterterm_matter_flux_residual_channel_ready"],
                "closure": matter_flux["closure"],
            },
        },
        "post_radius_embedding_channels": post_radius_channels,
        "open_non_GHY_channels": open_channels,
        "remaining_non_GHY_channel_absence_proved": all_known_zero and not any_open,
        "E_counterterm_zero_conditionally_allowed": all_known_zero and not any_open,
        "E_counterterm_ready": False,
        "decision": (
            "Known zero channels now include the Cartan-GHY linear K partition, "
            "torsion pullback, Immirzi radial contraction, local projected spinor "
            "residual, and the perfect-fluid tangential matter-flux residual. "
            f"Open non-GHY channels remain: {', '.join(open_labels)}. "
            "Embedding residual transport is tracked as a post-radius obligation, "
            "because the active embedding is produced only after R_Sigma(a). "
            "Therefore E_counterterm=0 is not yet proved."
        ),
        "next_required": [
            f"derive_or_eliminate_{label}"
            for label in open_labels
        ],
        "forbidden_shortcuts": [
            "do_not_treat_missing_channels_as_zero",
            "do_not_claim_E_counterterm_zero_until_absence_proved",
            "do_not_reintroduce_linear_K_counterterm",
        ],
        "output_manifest": str(output_path),
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Remaining Non-GHY Counterterm Channel Audit",
        "",
        payload["decision"],
        "",
        f"Absence proved: `{payload['remaining_non_GHY_channel_absence_proved']}`",
        f"E_counterterm zero conditionally allowed: `{payload['E_counterterm_zero_conditionally_allowed']}`",
        "",
        "## Open Channels",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["open_non_GHY_channels"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
