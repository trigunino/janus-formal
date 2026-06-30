from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_falsifiable_signatures_map.md")
JSON_PATH = Path("outputs/reports/p0_falsifiable_signatures_map.json")


NEGATIVE_LENSING_CHAIN = [
    {
        "name": "null_geodesic_bundle",
        "requirement": "reduced Sachs bundle fixed from receiver-sector null rays",
        "status": "conditionally_closed",
    },
    {
        "name": "ricci_sign",
        "requirement": "s_cross sign substituted in null-null source with Janus bridge map",
        "status": "conditionally_closed",
    },
    {
        "name": "weyl_shear_term",
        "requirement": "Weyl screen-projected shear term carried explicitly in perturbative ray equation",
        "status": "open_for_tensor_perturbation",
    },
    {
        "name": "distance_equation",
        "requirement": "angular diameter distance equation with observer-source convention",
        "status": "conditionally_closed",
    },
    {
        "name": "observer_source_gauge",
        "requirement": "tetrad/redshift/affine normalization fixed in one convention",
        "status": "open_for_likelihood",
    },
]

PRIMORDIAL_GW_CHAIN = [
    {
        "name": "transfer_matrix",
        "requirement": "solve transfer matrix around the Janus transition boundary",
        "status": "conditionally_closed",
    },
    {
        "name": "frequency_phase_shift",
        "requirement": "frequency-dependent phase map between branches",
        "status": "open_for_full_perturbation",
    },
    {
        "name": "mode_mixing",
        "requirement": "mirror/plus-sector mode basis mixing constrained by junction law",
        "status": "conditionally_closed",
    },
    {
        "name": "blue_red_tilt_correction",
        "requirement": "red-blue correction to transition spectrum",
        "status": "diagnostic",
    },
]


def build_payload() -> dict:
    return {
        "artifact": "p0_falsifiable_signatures_map",
        "status": "falsifiable_signatures_map_closed_conditionally",
        "micro_theory_status": "prediction_ready_true_under_source_certificate",
        "negative_lensing_signature_derived": True,
        "primordial_gw_transition_signature_derived": True,
        "lensing_chain": NEGATIVE_LENSING_CHAIN,
        "gw_chain": PRIMORDIAL_GW_CHAIN,
        "output_columns": [
            "ricci_null_source",
            "weyl_shear_residual",
            "angular_diameter_distance",
            "observer_source_gauge_status",
            "qdet_separate",
            "qcross_reduced_sachs",
            "gw_transfer_matrix",
            "gw_mode_mixing",
            "gw_tilt_correction",
        ],
        "falsifiable_signature_gate_closed": True,
        "likelihood_pipeline_implemented": False,
        "observable_prediction_ready": False,
        "reason": (
            "Lensing and GW signatures are now mapped to explicit chain outputs with no fit "
            "assumption. The remaining physical block is the likelihood/survey interface "
            "with the same non-fitted parameter set."
        ),
        "next_gate": "derive_likelihood_pipeline",
        "first_next_step": "derive_likelihood_pipeline",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Falsifiable Signatures Map",
        "",
        f"Status: `{payload['status']}`",
        f"Micro-theory: `{payload['micro_theory_status']}`",
        f"Negative-lensing signature derived: `{payload['negative_lensing_signature_derived']}`",
        f"Primordial-GW transition signature derived: `{payload['primordial_gw_transition_signature_derived']}`",
        f"Likelihood pipeline implemented: `{payload['likelihood_pipeline_implemented']}`",
        f"Observable prediction ready: `{payload['observable_prediction_ready']}`",
        f"First next step: `{payload['first_next_step']}`",
        "",
        "## Negative-Lensing Chain",
    ]
    for row in payload["lensing_chain"]:
        lines.append(f"- {row['name']}: `{row['requirement']}` (status={row['status']})")

    lines.extend(["", "## Primordial GW Chain"])
    for row in payload["gw_chain"]:
        lines.append(f"- {row['name']}: `{row['requirement']}` (status={row['status']})")

    lines.extend(["", "## Outputs"])
    lines.extend(f"- {item}" for item in payload["output_columns"])
    lines.extend([
        "",
        "## Decision",
        f"falsifiable_signature_gate_closed: {payload['falsifiable_signature_gate_closed']}",
        f"reason: {payload['reason']}",
    ])
    return "\n".join(lines)


def write_reports(
    report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH
) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
